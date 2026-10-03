import Route

/-!
## Phase A — abstract fixed-row cut arithmetic

This file formalizes §4–§5 of the run-compressed notes without any string
structure.  We fix one row `ell : Nat → Int` (`ell e` = `ℓ_{t,e}`) and reason
about the `K`-owner cut and `Q`-owner cut routes purely arithmetically.
-/

namespace CutArith
open Route

/-- Normalized candidate route: a non-positive length collapses to `(0,-1)`. -/
def mk (len e : Int) : Route := if len ≤ 0 then unmatched else ⟨len, e⟩

theorem mk_pos (len e : Int) (h : 0 < len) : mk len e = ⟨len, e⟩ := by
  unfold mk; rw [if_neg (by omega)]

theorem mk_nonpos (len e : Int) (h : len ≤ 0) : mk len e = unmatched := by
  unfold mk; rw [if_pos h]

theorem valid_mk (len e : Int) (he : -1 ≤ e) : Valid (mk len e) := by
  unfold mk
  by_cases h : len ≤ 0
  · rw [if_pos h]; exact valid_unmatched
  · rw [if_neg h]
    unfold Valid; dsimp only
    exact ⟨by omega, he, by intro h0; omega⟩

theorem valid_pair (len e : Int) (hl : 0 < len) (he : -1 ≤ e) : Valid ⟨len, e⟩ := by
  unfold Valid; dsimp only
  exact ⟨by omega, he, by intro h0; omega⟩

/-- `δ_e = e - ℓ_e` (an `Int`, possibly `-1`). -/
def delta (ell : Nat → Int) (e : Nat) : Int := (e : Int) - ell e

/-! ### Per-endpoint deletion formula (K-single) -/

/-- Candidate route at endpoint `e` after deleting K owner `s`. -/
def kcutCand (ell : Nat → Int) (s e : Nat) : Route :=
  if e < s then mk (ell e) (e : Int)
  else if e = s then unmatched
  else mk (min (ell e) ((e : Int) - (s : Int))) (e : Int)

/-- Brute K-cut: pointwise max over `e < t` of the single-endpoint candidates. -/
def bruteKCut (ell : Nat → Int) (t s : Nat) : Route :=
  rmaxList ((List.range t).map fun e => kcutCand ell s e)

/-- The hook-split identity (§4.2): for `e > s`, `min(ℓ_e, e-s)` is `e-s` when
`δ_e ≤ s` and `ℓ_e` otherwise. -/
theorem hook_split (ell : Nat → Int) (s e : Nat) (hse : s < e) :
    min (ell e) ((e : Int) - (s : Int))
      = if (e : Int) - ell e ≤ (s : Int) then (e : Int) - (s : Int) else ell e := by
  by_cases h : (e : Int) - ell e ≤ (s : Int)
  · rw [if_pos h, Int.min_eq_right]; omega
  · rw [if_neg h, Int.min_eq_left]; omega

/-! ### Hook decomposition pieces -/

/-- `A(s)`: best candidate strictly left of the owner. -/
def apartList (ell : Nat → Int) (t s : Nat) : List Route :=
  (((List.range t).filter fun e => decide (e < s ∧ 0 < ell e)).map
    fun e => ⟨ell e, (e : Int)⟩)

/-- `P(s)`: best candidate `e > s` whose deletion does not truncate it (`δ_e > s`). -/
def ppartList (ell : Nat → Int) (t s : Nat) : List Route :=
  (((List.range t).filter fun e => decide (0 < ell e ∧ (s : Int) < (e : Int) - ell e)).map
    fun e => ⟨ell e, (e : Int)⟩)

/-- Endpoints eligible for the ramp/plateau term `R(s)` (`δ_e ≤ s`). -/
def uList (ell : Nat → Int) (t s : Nat) : List Int :=
  ((List.range t).filter fun e => decide (0 < ell e ∧ (e : Int) - ell e ≤ (s : Int))).map
    fun (e : Nat) => (e : Int)

/-- `U(s)`: maximal eligible endpoint (or `-1`). -/
def umax (ell : Nat → Int) (t s : Nat) : Int := (uList ell t s).foldr max (-1)

/-- `R(s)`: the ramp/plateau candidate from the maximal eligible endpoint. -/
def rpart (ell : Nat → Int) (t s : Nat) : Route :=
  if (s : Int) < umax ell t s then mk (umax ell t s - (s : Int)) (umax ell t s) else unmatched

/-! ### List max lemmas for `Int` folds -/

theorem le_foldr_max (l : List Int) : ∀ x ∈ l, x ≤ l.foldr max (-1) := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons y ys ih =>
    intro x hx
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact Int.le_max_left _ _
    · exact Int.le_trans (ih x h) (Int.le_max_right _ _)

theorem neg_one_le_foldr_max (l : List Int) : -1 ≤ l.foldr max (-1) := by
  induction l with
  | nil => simp
  | cons y ys ih => rw [List.foldr_cons]; exact Int.le_trans ih (Int.le_max_right _ _)

theorem mem_uList {ell : Nat → Int} {t s e : Nat} :
    (e : Int) ∈ uList ell t s ↔ e < t ∧ 0 < ell e ∧ (e : Int) - ell e ≤ (s : Int) := by
  unfold uList
  rw [List.mem_map]
  constructor
  · rintro ⟨e', he', h⟩
    rw [List.mem_filter] at he'
    obtain ⟨hm, hp⟩ := he'
    rw [List.mem_range] at hm
    simp only [decide_eq_true_eq] at hp
    have : e' = e := by omega
    subst this
    exact ⟨hm, hp.1, hp.2⟩
  · rintro ⟨hm, h1, h2⟩
    exact ⟨e, by rw [List.mem_filter]; exact ⟨by rw [List.mem_range]; exact hm, by simp [h1, h2]⟩, rfl⟩

theorem mem_apartList {ell : Nat → Int} {t s e : Nat} :
    (⟨ell e, (e : Int)⟩ : Route) ∈ apartList ell t s ↔ e < t ∧ e < s ∧ 0 < ell e := by
  unfold apartList
  rw [List.mem_map]
  constructor
  · rintro ⟨e', he', h⟩
    rw [List.mem_filter] at he'
    obtain ⟨hm, hp⟩ := he'
    rw [List.mem_range] at hm
    simp only [decide_eq_true_eq] at hp
    have : e' = e := by
      have := congrArg Route.endpoint h; simp at this; omega
    subst this
    exact ⟨hm, hp.1, hp.2⟩
  · rintro ⟨hm, h1, h2⟩
    exact ⟨e, by rw [List.mem_filter]; exact ⟨by rw [List.mem_range]; exact hm, by simp [h1, h2]⟩, rfl⟩

theorem mem_ppartList {ell : Nat → Int} {t s e : Nat} :
    (⟨ell e, (e : Int)⟩ : Route) ∈ ppartList ell t s ↔
      e < t ∧ 0 < ell e ∧ (s : Int) < (e : Int) - ell e := by
  unfold ppartList
  rw [List.mem_map]
  constructor
  · rintro ⟨e', he', h⟩
    rw [List.mem_filter] at he'
    obtain ⟨hm, hp⟩ := he'
    rw [List.mem_range] at hm
    simp only [decide_eq_true_eq] at hp
    have : e' = e := by
      have := congrArg Route.endpoint h; simp at this; omega
    subst this
    exact ⟨hm, hp.1, hp.2⟩
  · rintro ⟨hm, h1, h2⟩
    exact ⟨e, by rw [List.mem_filter]; exact ⟨by rw [List.mem_range]; exact hm, by simp [h1, h2]⟩, rfl⟩


theorem foldr_max_mem (l : List Int) (hne : l ≠ []) (hb : ∀ x ∈ l, -1 ≤ x) :
    l.foldr max (-1) ∈ l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    rw [List.foldr_cons]
    by_cases hys : ys = []
    · subst hys
      rw [List.foldr_nil, Int.max_eq_left (hb y (by simp))]
      exact List.mem_cons_self
    · have hy : ys.foldr max (-1) ∈ ys :=
        ih (by simp [hys]) (fun x hx => hb x (by simp [hx]))
      by_cases hle : y ≤ ys.foldr max (-1)
      · rw [Int.max_eq_right hle]
        exact List.mem_cons_of_mem y hy
      · rw [Int.max_eq_left (by omega)]
        exact List.mem_cons_self

end CutArith

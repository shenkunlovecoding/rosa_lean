import Std
import Lcs
import RunRectangle

/-!
## Phase F — One-bit repair Boundary-Support (§9.3)

Inside a `α≠β` run rectangle the non-trivial repair context only lives on the
four boundary edges: strict interior pairs have `L = R = 0`.
-/

open Lcs RunRect

set_option linter.unusedSectionVars false

namespace Repair

variable {α : Type} [DecidableEq α]

/-- `PrefixEq q k Tq Tk p u R`: the length-`R` forward context after `(p,u)` matches. -/
def PrefixEq (q k : Nat → α) (Tq Tk p u R : Nat) : Prop :=
  R ≤ Tq - p - 1 ∧ R ≤ Tk - u - 1 ∧ ∀ h ∈ List.range R, q (p + 1 + h) = k (u + 1 + h)

theorem prefixEq_zero (q k : Nat → α) (Tq Tk p u : Nat) : PrefixEq q k Tq Tk p u 0 := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
  intro h hh; simp at hh

theorem prefixEq_mono {q k : Nat → α} {Tq Tk p u R R' : Nat}
    (h : PrefixEq q k Tq Tk p u R) (hR : R' ≤ R) : PrefixEq q k Tq Tk p u R' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  intro h' hh
  rw [List.mem_range] at hh
  exact h3 h' (List.mem_range.mpr (by omega))

theorem prefixEq_max {q k : Nat → α} {Tq Tk p u a b : Nat}
    (ha : PrefixEq q k Tq Tk p u a) (hb : PrefixEq q k Tq Tk p u b) :
    PrefixEq q k Tq Tk p u (max a b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨by omega, by omega, ?_⟩
  intro h hh
  rw [List.mem_range] at hh
  rcases Nat.le_total a b with hab | hba
  · exact hb3 h (List.mem_range.mpr (by omega))
  · exact ha3 h (List.mem_range.mpr (by omega))

theorem prefixEq_iff_all (q k : Nat → α) (Tq Tk p u R : Nat) :
    PrefixEq q k Tq Tk p u R ↔
      R ≤ Tq - p - 1 ∧ R ≤ Tk - u - 1 ∧
        (List.range R).all (fun h => decide (q (p + 1 + h) = k (u + 1 + h))) = true := by
  unfold PrefixEq
  constructor
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, ?_⟩
    rw [List.all_eq_true]
    intro x hx
    rw [decide_eq_true_eq]
    exact c x hx
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, ?_⟩
    intro x hx
    have h := (List.all_eq_true.mp c) x hx
    rwa [decide_eq_true_eq] at h

instance (q k : Nat → α) (Tq Tk p u R : Nat) : Decidable (PrefixEq q k Tq Tk p u R) :=
  decidable_of_iff'
    (R ≤ Tq - p - 1 ∧ R ≤ Tk - u - 1 ∧
      (List.range R).all (fun h => decide (q (p + 1 + h) = k (u + 1 + h))) = true)
    (prefixEq_iff_all q k Tq Tk p u R)

def maxPrefix (q k : Nat → α) (Tq Tk p u : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if PrefixEq q k Tq Tk p u n then max n (maxPrefix q k Tq Tk p u n)
             else maxPrefix q k Tq Tk p u n

/-- `lcpLen`: the maximal forward context length after `(p,u)`. -/
def lcpLen (q k : Nat → α) (Tq Tk p u : Nat) : Nat :=
  maxPrefix q k Tq Tk p u (min (Tq - p - 1) (Tk - u - 1) + 1)

theorem maxPrefix_spec (q k : Nat → α) (Tq Tk p u : Nat) :
    ∀ n, PrefixEq q k Tq Tk p u (maxPrefix q k Tq Tk p u n) := by
  intro n
  induction n with
  | zero => rw [maxPrefix]; exact prefixEq_zero q k Tq Tk p u
  | succ m ih =>
    rw [maxPrefix]
    by_cases h : PrefixEq q k Tq Tk p u m
    · rw [if_pos h]; exact prefixEq_max h ih
    · rw [if_neg h]; exact ih

theorem maxPrefix_le (q k : Nat → α) (Tq Tk p u : Nat) :
    ∀ n m, (∀ R, R < n → PrefixEq q k Tq Tk p u R → R ≤ m) →
      maxPrefix q k Tq Tk p u n ≤ m := by
  intro n
  induction n with
  | zero => intro m _; rw [maxPrefix]; exact Nat.zero_le m
  | succ n ih =>
    intro m h
    rw [maxPrefix]
    by_cases hc : PrefixEq q k Tq Tk p u n
    · rw [if_pos hc]
      have h1 : n ≤ m := h n (by omega) hc
      have h2 : maxPrefix q k Tq Tk p u n ≤ m := ih m (fun R hR hs => h R (by omega) hs)
      omega
    · rw [if_neg hc]
      exact ih m (fun R hR hs => h R (by omega) hs)

theorem maxPrefix_greatest (q k : Nat → α) (Tq Tk p u : Nat) :
    ∀ n R, PrefixEq q k Tq Tk p u R → R < n → R ≤ maxPrefix q k Tq Tk p u n := by
  intro n
  induction n with
  | zero => intro R _ hR; omega
  | succ n ih =>
    intro R hs hR
    rw [maxPrefix]
    by_cases hc : PrefixEq q k Tq Tk p u n
    · rw [if_pos hc]
      have hcase : R = n ∨ R < n := by omega
      rcases hcase with heq | hlt
      · subst heq; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih R hs hlt) (Nat.le_max_right _ _)
    · rw [if_neg hc]
      have hlt : R < n := by
        have hcase : R = n ∨ R < n := by omega
        rcases hcase with heq | hlt
        · subst heq; exact absurd hs hc
        · exact hlt
      exact ih R hs hlt

theorem lcpLen_spec (q k : Nat → α) (Tq Tk p u : Nat) :
    PrefixEq q k Tq Tk p u (lcpLen q k Tq Tk p u) :=
  maxPrefix_spec q k Tq Tk p u _

theorem lcpLen_greatest {q k : Nat → α} {Tq Tk p u R : Nat}
    (h : PrefixEq q k Tq Tk p u R) : R ≤ lcpLen q k Tq Tk p u := by
  apply maxPrefix_greatest
  · exact h
  · have h1 := h.1; have h2 := h.2.1; omega

/-- Positive forward context forces the first symbol to match. -/
theorem lcpLen_pos_eq {q k : Nat → α} {Tq Tk p u : Nat}
    (h : 0 < lcpLen q k Tq Tk p u) : q (p + 1) = k (u + 1) := by
  have hs := lcpLen_spec q k Tq Tk p u
  have h0 : 0 ∈ List.range (lcpLen q k Tq Tk p u) := List.mem_range.mpr h
  have := hs.2.2 0 h0
  simpa using this

/-- Positive suffix context forces the last symbol to match. -/
theorem lcsLen_pos_eq {q k : Nat → α} {t e : Nat} (h : 0 < lcsLen q k t e) :
    q t = k e := by
  have hs := lcsLen_spec q k t e
  have h0 : 0 ∈ List.range (lcsLen q k t e) := List.mem_range.mpr h
  have := hs.2.2 0 h0
  simpa using this

/-! ### Boundary-Support -/

/-- `BS-L`: a non-trivial left context lives on the Q-left or K-left edge. -/
theorem repair_left_boundary_support {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d)
    (hpos : 0 < lcsLen q k (p - 1) (u - 1)) :
    p = a ∨ u = c := by
  by_cases hpa : p = a
  · exact Or.inl hpa
  by_cases huc : u = c
  · exact Or.inr huc
  exfalso
  have hpgt : a < p := by omega
  have hugt : c < u := by omega
  have hpq : q (p - 1) = αs := hQ.mem (p - 1) (by omega) (by omega)
  have huk : k (u - 1) = βs := hK.mem (u - 1) (by omega) (by omega)
  have heq := lcsLen_pos_eq hpos
  exact hne (by rw [← hpq, heq, huk])

/-- `BS-R`: a non-trivial right context lives on the Q-right or K-right edge. -/
theorem repair_right_boundary_support {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d)
    (hpos : 0 < lcpLen q k Tq Tk p u) :
    p = b ∨ u = d := by
  by_cases hpb' : p = b
  · exact Or.inl hpb'
  by_cases hud' : u = d
  · exact Or.inr hud'
  exfalso
  have hplt : p < b := by omega
  have hult : u < d := by omega
  have hpq : q (p + 1) = αs := hQ.mem (p + 1) (by omega) (by omega)
  have huk : k (u + 1) = βs := hK.mem (u + 1) (by omega) (by omega)
  have heq := lcpLen_pos_eq hpos
  exact hne (by rw [← hpq, heq, huk])

/-- Strict interior of a `α≠β` rectangle has both contexts trivial. -/
theorem repair_strict_interior_trivial {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p u : Nat} (hpa : a < p) (hpb : p < b) (huc : c < u) (hud : u < d) :
    lcsLen q k (p - 1) (u - 1) = 0 ∧ lcpLen q k Tq Tk p u = 0 := by
  constructor
  · have hz : ¬ 0 < lcsLen q k (p - 1) (u - 1) := fun hpos =>
      absurd (repair_left_boundary_support hQ hK hne (by omega) (by omega) (by omega) (by omega) hpos)
        (by omega)
    omega
  · have hz : ¬ 0 < lcpLen q k Tq Tk p u := fun hpos =>
      absurd (repair_right_boundary_support hQ hK hne (by omega) (by omega) (by omega) (by omega) hpos)
        (by omega)
    omega

/-- Phase G / item 10: the left-edge Q run.  For the current one-bit rectangle
with Q-left edge `p = a = bp+1`, the left context `L(a,u) = lcsLen q k (a-1) (u-1)`
is ramp / spike / plateau in `u`, i.e. the Run-Rectangle RSP shape applied to the
previous Q run `[ap,bp]` against the current K run `[c,d]`. -/
theorem repair_edge_left_rsp {q k : Nat → α} {Tq Tk ap bp c d : Nat} {αs' βs : α}
    (hQp : ConstRun q Tq ap bp αs') (hK : ConstRun k Tk c d βs) (heq : αs' = βs)
    (hab : ap ≤ bp) (hap : 0 < ap) (hc : 0 < c)
    {u : Nat} (huc : c < u) (hud : u ≤ d) :
    lcsLen q k bp (u - 1) =
      (if u - c < bp - ap + 1 then u - c
       else if u - c = bp - ap + 1 then (bp - ap + 1) + lcsLen q k (ap - 1) (c - 1)
       else bp - ap + 1) := by
  have he1 : c ≤ u - 1 := by omega
  have he2 : u - 1 ≤ d := by omega
  have h := run_rectangle_rsp (t := bp) (e := u - 1) hQp hK heq hap hc hab
    (Nat.le_refl bp) he1 he2
  rw [h, show (u - 1) - c + 1 = u - c by omega]

/-! ### Causal-centre contexts with underflow guards

`lcsLen q k (p-1) (u-1)` **underflows** when `p = 0` or `u = 0` (there is no left
character), silently comparing `k 0`.  `leftCtx` guards this.  The right context
`lcpLen q k Tq Tk p u` needs no guard (it reads `p+1`, `u+1`). -/

/-- Left context of a causal centre `(p,u)`: `0` when either side has no left
character, otherwise the LCSuffix of the prefixes before `p` and `u`. -/
def leftCtx (q k : Nat → α) (p u : Nat) : Nat :=
  if p = 0 ∨ u = 0 then 0 else lcsLen q k (p - 1) (u - 1)

/-- Forward (right) context of a causal centre `(p,u)`. -/
def rightCtx (q k : Nat → α) (Tq Tk p u : Nat) : Nat := lcpLen q k Tq Tk p u

theorem leftCtx_eq {q k : Nat → α} {p u : Nat} (hp : 0 < p) (hu : 0 < u) :
    leftCtx q k p u = lcsLen q k (p - 1) (u - 1) := by
  unfold leftCtx; rw [if_neg]; omega

theorem leftCtx_zero {q k : Nat → α} {p u : Nat} (h : p = 0 ∨ u = 0) :
    leftCtx q k p u = 0 := by
  unfold leftCtx; rw [if_pos h]

/-- Base case of the run-grid recurrence (RG): if the current Q run or K run is
the first (`a = 0` or `c = 0`) the diagonal predecessor prefix is empty, so
`γ = 0`.  This closes the `0 < ap`/`0 < cp` coverage gap of
`RunRect.run_grid_gamma_recurrence`. -/
theorem run_grid_gamma_base {q k : Nat → α} {a c : Nat} (h : a = 0 ∨ c = 0) :
    leftCtx q k a c = 0 := leftCtx_zero h

end Repair

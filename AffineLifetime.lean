import Std
import AffineEnvelope
import RosBridge

/-!
## Affine winner envelopes with lifetimes

`OwnerEnvelope` proves interval structure only when every affine candidate is
active forever.  Real bridges have a birth and a death, so that conclusion is
not available.  This file supplies the lifetime replacement:

* the active lexicographic winner is defined pointwise;
* births, deaths, and pairwise affine crossing windows form a finite critical
  event list;
* winner identity is constant between consecutive critical events;
* therefore every winner change is covered by the finite list.

The statement is deliberately local in time.  There is no interval/single-piece
claim, and the two-candidate example at the end records that winner re-entry is
allowed.
-/

namespace AffineLifetime

open AffEnv
open AffEnv.AffRoute

/-! ### Candidates and pointwise winners -/

/-- A finite affine candidate living on the closed integer interval
`[birth, death]`. -/
structure Candidate where
  route : AffRoute
  birth : Int
  death : Int
  deriving DecidableEq, Repr

namespace Candidate

/-- The candidate exists at time `t`. -/
def Active (c : Candidate) (t : Int) : Prop := c.birth ≤ t ∧ t ≤ c.death

instance (c : Candidate) (t : Int) : Decidable (c.Active t) := by
  unfold Active
  infer_instance

end Candidate

/-- `c` is an active lexicographic winner among the finite candidate list. -/
def Winner (c : Candidate) (cs : List Candidate) (t : Int) : Prop :=
  c ∈ cs ∧ c.Active t ∧
    ∀ d ∈ cs, d.Active t → c.route.wins d.route t

/-- Extensional equality of the pointwise winner set at two times. -/
def SameWinnerSet (cs : List Candidate) (t s : Int) : Prop :=
  ∀ c, Winner c cs t ↔ Winner c cs s

theorem sameWinnerSet_refl (cs : List Candidate) (t : Int) : SameWinnerSet cs t t := by
  intro c
  rfl

theorem sameWinnerSet_symm {cs : List Candidate} {t s : Int}
    (h : SameWinnerSet cs t s) : SameWinnerSet cs s t := by
  intro c
  exact (h c).symm

theorem sameWinnerSet_trans {cs : List Candidate} {t s u : Int}
    (hts : SameWinnerSet cs t s) (hsu : SameWinnerSet cs s u) : SameWinnerSet cs t u := by
  intro c
  exact (hts c).trans (hsu c)

/-! ### Adapter for concrete ROSA bridges -/

open RosBridge

/-- Forget the `Nat`-specific bridge representation to the abstract affine
lifetime candidate used by this file. -/
def ofBridge (b : Bridge) : Candidate :=
  ⟨⟨1, (b.L : Int) + 1 - (b.p : Int), 1, (b.u : Int) - (b.p : Int)⟩,
    (b.p : Int), (b.death : Int)⟩

theorem ofBridge_active_nat_iff (b : Bridge) (t : Nat) :
    (ofBridge b).Active (t : Int) ↔ b.Active t := by
  dsimp [Candidate.Active, ofBridge]
  change ((b.p : Int) ≤ (t : Int) ∧ (t : Int) ≤ (b.death : Int)) ↔
    b.p ≤ t ∧ t ≤ b.p + b.R
  unfold RosBridge.Bridge.death
  constructor <;> intro h <;> omega

theorem ofBridge_routeAt_len (b : Bridge) (t : Nat) (h : b.Active t) :
    (ofBridge b).route.len (t : Int) = (b.routeAt t).len := by
  dsimp only [ofBridge, AffRoute.len, RosBridge.Bridge.routeAt]
  have ht : b.p ≤ t := h.1
  have hcast : ((b.L + 1 + (t - b.p) : Nat) : Int) =
      (b.L : Int) + 1 + ((t : Int) - (b.p : Int)) := by omega
  rw [hcast]
  omega

theorem ofBridge_routeAt_ep (b : Bridge) (t : Nat) (h : b.Active t) :
    (ofBridge b).route.ep (t : Int) = (b.routeAt t).endpoint := by
  dsimp only [ofBridge, AffRoute.ep, RosBridge.Bridge.routeAt]
  have ht : b.p ≤ t := h.1
  have hcast : ((b.u + (t - b.p) : Nat) : Int) =
      (b.u : Int) + ((t : Int) - (b.p : Int)) := by omega
  rw [hcast]
  omega

theorem ofBridge_routeAt_eq (b : Bridge) (t : Nat) (h : b.Active t) :
    (⟨(ofBridge b).route.len (t : Int), (ofBridge b).route.ep (t : Int)⟩ : Route) =
      b.routeAt t := by
  apply Route.ext
  · exact ofBridge_routeAt_len b t h
  · exact ofBridge_routeAt_ep b t h

/-- The abstract affine winner used in this file agrees with ROSA's `Route.rle`
for two concrete bridges at a common active time. -/
theorem ofBridge_wins_iff_route_rle (b c : Bridge) (t : Nat)
    (hb : b.Active t) (hc : c.Active t) :
    (ofBridge b).route.wins (ofBridge c).route (t : Int) ↔
      Route.rle (c.routeAt t) (b.routeAt t) := by
  unfold AffRoute.wins Route.rle
  rw [ofBridge_routeAt_len b t hb, ofBridge_routeAt_len c t hc,
    ofBridge_routeAt_ep b t hb, ofBridge_routeAt_ep c t hc]
  constructor
  · intro h
    rcases h with hlen | ⟨heq, hep⟩
    · left; omega
    · right; exact ⟨heq.symm, hep⟩
  · intro h
    rcases h with hlen | ⟨heq, hep⟩
    · left; omega
    · right; exact ⟨heq.symm, hep⟩

/-! ### Pairwise affine crossing windows -/

/-- The two consecutive integer times covering the zero of `s*t+b`, for
`s > 0`. -/
def posRootWindow (s b : Int) : List Int :=
  let r := (-b) / s
  [r, r + 1]

/-- Normalized crossing window for a negative slope `s < 0`. -/
def negRootWindow (s b : Int) : List Int :=
  posRootWindow (-s) (-b)

/-- Critical times for one ordered pair of affine routes.  The two-point
window handles exact integer roots without committing to a particular rounding
direction. -/
def pairCritical (a b : Candidate) : List Int :=
  let A := a.route.aL - b.route.aL
  let B := a.route.bL - b.route.bL
  if 0 < A then
    posRootWindow A B
  else if A < 0 then
    negRootWindow A B
  else if B = 0 then
    let C := a.route.aE - b.route.aE
    let D := a.route.bE - b.route.bE
    if 0 < C then
      posRootWindow C D
    else if C < 0 then
      negRootWindow C D
    else
      []
  else
    []

/-- Lexicographic priority on a length difference `L` and endpoint difference
`E`: larger `L`, then larger `E` on `L = 0`. -/
def LexRel (L E : Int) : Prop := L > 0 ∨ (L = 0 ∧ E ≥ 0)

/-- Any positive-slope affine zero crossing between `t` and `t+1` lies in the
two-point crossing window. -/
theorem succ_mem_posRootWindow_of_nonpos_nonneg {s b t : Int}
    (hs : 0 < s) (hlo : s * t + b ≤ 0) (hhi : 0 ≤ s * (t + 1) + b) :
    t + 1 ∈ posRootWindow s b := by
  let r := (-b) / s
  have htr : t ≤ r := by
    dsimp [r]
    rw [Int.le_ediv_iff_mul_le hs]
    have h' : s * t ≤ -b := by omega
    rwa [Int.mul_comm t s]
  have hrt : r ≤ t + 1 := by
    dsimp [r]
    rw [Int.ediv_le_iff_le_mul hs]
    have h' : -b ≤ s * (t + 1) := by omega
    have hlt : -b < s * (t + 1) + s := by omega
    simpa [Int.mul_comm (t + 1) s] using hlt
  simp only [posRootWindow, List.mem_cons, List.mem_nil_iff, or_false]
  omega

/-- Positive-slope nonnegativity cannot change across a step outside its
crossing window. -/
theorem pos_nonneg_succ_iff {s b t : Int} (hs : 0 < s)
    (hnot : t + 1 ∉ posRootWindow s b) :
    (0 ≤ s * (t + 1) + b ↔ 0 ≤ s * t + b) := by
  have hnotCross : ¬ (s * t + b ≤ 0 ∧ 0 ≤ s * (t + 1) + b) := by
    intro hc
    exact hnot (succ_mem_posRootWindow_of_nonpos_nonneg hs hc.1 hc.2)
  have hnext : s * (t + 1) + b = s * t + b + s := by
    rw [Int.mul_add, Int.mul_one]
    omega
  have hcase : 0 < s * t + b ∨ s * t + b + s < 0 := by omega
  rw [hnext]
  constructor <;> intro h <;> rcases hcase with hp | hn <;> omega

/-- Negative-slope version of `pos_nonneg_succ_iff`. -/
theorem neg_nonneg_succ_iff {s b t : Int} (hs : s < 0)
    (hnot : t + 1 ∉ negRootWindow s b) :
    (0 ≤ s * (t + 1) + b ↔ 0 ≤ s * t + b) := by
  have hp : 0 < -s := by omega
  have hnot' : t + 1 ∉ posRootWindow (-s) (-b) := by
    simpa [negRootWindow] using hnot
  have hnotCross : ¬ ((-s) * t + (-b) ≤ 0 ∧
      0 ≤ (-s) * (t + 1) + (-b)) := by
    intro hc
    exact hnot' (succ_mem_posRootWindow_of_nonpos_nonneg hp hc.1 hc.2)
  have hnotCross' : ¬ (0 ≤ s * t + b ∧ s * (t + 1) + b ≤ 0) := by
    intro hc
    apply hnotCross
    constructor <;> simp only [Int.neg_mul] <;> omega
  have hnext : s * (t + 1) + b = s * t + b + s := by
    rw [Int.mul_add, Int.mul_one]
    omega
  have hcase : s * t + b < 0 ∨ 0 < s * (t + 1) + b := by omega
  rw [hnext]
  constructor <;> intro h <;> rcases hcase with hn | hp' <;> omega

/-- Positive length slope: the lexicographic relation is stable outside the
length crossing window. -/
theorem lex_pos_succ_iff {A C L E t : Int} (hA : 0 < A)
    (hnot : t + 1 ∉ posRootWindow A (L - A * t)) :
    LexRel (L + A) (E + C) ↔ LexRel L E := by
  have hnext : L + A = A * (t + 1) + (L - A * t) := by
    rw [Int.mul_add, Int.mul_one]
    omega
  have hnotCross : ¬ (A * t + (L - A * t) ≤ 0 ∧
      0 ≤ A * (t + 1) + (L - A * t)) := by
    intro hc
    exact hnot (succ_mem_posRootWindow_of_nonpos_nonneg hA hc.1 hc.2)
  have hnotCross' : ¬ (L ≤ 0 ∧ 0 ≤ L + A) := by
    intro hc
    apply hnotCross
    constructor <;> omega
  have hcase : 0 < L ∨ L + A < 0 := by omega
  unfold LexRel
  constructor <;> intro h
  · rcases hcase with hp | hn
    · exact Or.inl hp
    · rcases h with hlen | ⟨heq, _⟩ <;> omega
  · rcases hcase with hp | hn
    · exact Or.inl (by omega)
    · rcases h with hlen | ⟨heq, _⟩ <;> omega

/-- Negative length slope version. -/
theorem lex_neg_succ_iff {A C L E t : Int} (hA : A < 0)
    (hnot : t + 1 ∉ negRootWindow A (L - A * t)) :
    LexRel (L + A) (E + C) ↔ LexRel L E := by
  have hp : 0 < -A := by omega
  have hnext : L + A = A * (t + 1) + (L - A * t) := by
    rw [Int.mul_add, Int.mul_one]
    omega
  have hnot' : t + 1 ∉ posRootWindow (-A) (-(L - A * t)) := by
    simpa [negRootWindow] using hnot
  have hnotCross : ¬ ((-A) * t + (-(L - A * t)) ≤ 0 ∧
      0 ≤ (-A) * (t + 1) + (-(L - A * t))) := by
    intro hc
    exact hnot' (succ_mem_posRootWindow_of_nonpos_nonneg hp hc.1 hc.2)
  have hnotCross' : ¬ (0 ≤ L ∧ L + A ≤ 0) := by
    intro hc
    apply hnotCross
    constructor <;> simp only [Int.neg_mul] <;> omega
  have hcase : L < 0 ∨ 0 < L + A := by omega
  unfold LexRel
  constructor <;> intro h
  · rcases hcase with hn | hp'
    · rcases h with hlen | ⟨heq, _⟩ <;> omega
    · exact Or.inl (by omega)
  · rcases hcase with hn | hp'
    · rcases h with hlen | ⟨heq, _⟩ <;> omega
    · exact Or.inl (by omega)

/-- Reflexivity of the Route winner relation. -/
theorem aff_wins_refl (a : AffRoute) (t : Int) : a.wins a t := by
  unfold AffRoute.wins
  exact Or.inr ⟨rfl, by omega⟩

/-- Pair priority is stable across a step outside the pair's critical window. -/
theorem aff_wins_succ_iff_of_not_pairCritical {a b : Candidate} {t : Int}
    (hnot : t + 1 ∉ pairCritical a b) :
    (a.route.wins b.route (t + 1) ↔ a.route.wins b.route t) := by
  let A := a.route.aL - b.route.aL
  let B := a.route.bL - b.route.bL
  let C := a.route.aE - b.route.aE
  let D := a.route.bE - b.route.bE
  have hLen (u : Int) :
      a.route.wins b.route u ↔ LexRel (A * u + B) (C * u + D) := by
    rw [AffRoute.wins_iff]
    rfl
  have hB : B = (a.route.len t - b.route.len t) - A * t := by
    have h := AffRoute.len_diff a.route b.route t
    dsimp [A, B]
    omega
  by_cases hApos : 0 < A
  · rw [hLen (t + 1), hLen t]
    have hnotB : t + 1 ∉ posRootWindow A B := by
      have hAraw : 0 < a.route.aL - b.route.aL := by simpa [A] using hApos
      unfold pairCritical at hnot
      rw [if_pos hAraw] at hnot
      simpa [A, B] using hnot
    have hnot' : t + 1 ∉ posRootWindow A ((a.route.len t - b.route.len t) - A * t) := by
      simpa [hB] using hnotB
    have hnext : A * (t + 1) + B = (A * t + B) + A := by
      rw [Int.mul_add, Int.mul_one]
      omega
    have hend : C * (t + 1) + D = (C * t + D) + C := by
      rw [Int.mul_add, Int.mul_one]
      omega
    rw [hnext, hend]
    have hL : A * t + B = a.route.len t - b.route.len t := by
      simpa [A, B] using (AffRoute.len_diff a.route b.route t).symm
    simpa [hL] using
      lex_pos_succ_iff (L := a.route.len t - b.route.len t) (E := C * t + D) hApos hnot'
  · by_cases hAneg : A < 0
    · rw [hLen (t + 1), hLen t]
      have hnotB : t + 1 ∉ negRootWindow A B := by
        have hArawPos : ¬ 0 < a.route.aL - b.route.aL := by simpa [A] using hApos
        have hArawNeg : a.route.aL - b.route.aL < 0 := by simpa [A] using hAneg
        unfold pairCritical at hnot
        rw [if_neg hArawPos, if_pos hArawNeg] at hnot
        simpa [A, B] using hnot
      have hnot' : t + 1 ∉ negRootWindow A ((a.route.len t - b.route.len t) - A * t) := by
        simpa [hB] using hnotB
      have hnext : A * (t + 1) + B = (A * t + B) + A := by
        rw [Int.mul_add, Int.mul_one]
        omega
      have hend : C * (t + 1) + D = (C * t + D) + C := by
        rw [Int.mul_add, Int.mul_one]
        omega
      rw [hnext, hend]
      have hL : A * t + B = a.route.len t - b.route.len t := by
        simpa [A, B] using (AffRoute.len_diff a.route b.route t).symm
      simpa [hL] using
        lex_neg_succ_iff (L := a.route.len t - b.route.len t) (E := C * t + D) hAneg hnot'
    · have hAzero : A = 0 := by omega
      by_cases hBzero : B = 0
      · have hLt : a.route.len t - b.route.len t = 0 := by
          have h' := hB
          rw [hBzero, hAzero] at h'
          simp at h'
          omega
        rw [hLen (t + 1), hLen t]
        have hAt : A * t + B = 0 := by simp [hAzero, hBzero]
        have hAn : A * (t + 1) + B = 0 := by simp [hAzero, hBzero]
        rw [hAt, hAn]
        by_cases hCpos : 0 < C
        · have hnotC : t + 1 ∉ posRootWindow C D := by
            have hArawPos : ¬ 0 < a.route.aL - b.route.aL := by simpa [A] using hApos
            have hArawNeg : ¬ a.route.aL - b.route.aL < 0 := by simpa [A] using hAneg
            have hBraw : a.route.bL - b.route.bL = 0 := by simpa [B] using hBzero
            have hCraw : 0 < a.route.aE - b.route.aE := by simpa [C] using hCpos
            unfold pairCritical at hnot
            rw [if_neg hArawPos, if_neg hArawNeg, if_pos hBraw, if_pos hCraw] at hnot
            simpa [C, D] using hnot
          have hnext : C * (t + 1) + D = C * t + D + C := by
            rw [Int.mul_add, Int.mul_one]
            omega
          exact (by simpa [hnext, LexRel] using pos_nonneg_succ_iff hCpos hnotC)
        · by_cases hCneg : C < 0
          · have hnotC : t + 1 ∉ negRootWindow C D := by
              have hArawPos : ¬ 0 < a.route.aL - b.route.aL := by simpa [A] using hApos
              have hArawNeg : ¬ a.route.aL - b.route.aL < 0 := by simpa [A] using hAneg
              have hBraw : a.route.bL - b.route.bL = 0 := by simpa [B] using hBzero
              have hCrawPos : ¬ 0 < a.route.aE - b.route.aE := by simpa [C] using hCpos
              have hCrawNeg : a.route.aE - b.route.aE < 0 := by simpa [C] using hCneg
              unfold pairCritical at hnot
              rw [if_neg hArawPos, if_neg hArawNeg, if_pos hBraw, if_neg hCrawPos,
                if_pos hCrawNeg] at hnot
              simpa [C, D] using hnot
            have hnext : C * (t + 1) + D = C * t + D + C := by
              rw [Int.mul_add, Int.mul_one]
              omega
            exact (by simpa [hnext, LexRel] using neg_nonneg_succ_iff hCneg hnotC)
          · have hCzero : C = 0 := by omega
            simp [LexRel, hCzero]
      · have hAt : A * t + B = B := by simp [hAzero]
        have hAn : A * (t + 1) + B = B := by simp [hAzero]
        rw [hLen (t + 1), hLen t, hAt, hAn]
        constructor <;> intro h <;> unfold LexRel at h ⊢ <;> omega

/-! ### Finite critical events -/

/-- The two lifetime events of one candidate.  `death + 1` is the first time
after the closed lifetime. -/
def candidateEvents (c : Candidate) : List Int :=
  [c.birth, c.death + 1]

/-- All ordered-pair affine crossing windows in a finite candidate list. -/
def pairEvents (cs : List Candidate) : List Int :=
  List.flatMap (fun a => List.flatMap (fun b => pairCritical a b) cs) cs

/-- Finite critical event list.  Redundancy is intentional: this theorem is a
coverage result, not a deduplicated scan optimizer. -/
def criticalEvents (cs : List Candidate) : List Int :=
  List.flatMap candidateEvents cs ++ pairEvents cs

theorem birth_mem_criticalEvents {c : Candidate} {cs : List Candidate}
    (hc : c ∈ cs) : c.birth ∈ criticalEvents cs := by
  rw [criticalEvents, List.mem_append]
  left
  rw [List.mem_flatMap]
  exact ⟨c, hc, by simp [candidateEvents]⟩

theorem deathSucc_mem_criticalEvents {c : Candidate} {cs : List Candidate}
    (hc : c ∈ cs) : c.death + 1 ∈ criticalEvents cs := by
  rw [criticalEvents, List.mem_append]
  left
  rw [List.mem_flatMap]
  exact ⟨c, hc, by simp [candidateEvents]⟩

theorem pairCritical_mem_criticalEvents {a b : Candidate} {cs : List Candidate}
    (ha : a ∈ cs) (hb : b ∈ cs) {q : Int} (hq : q ∈ pairCritical a b) :
    q ∈ criticalEvents cs := by
  rw [criticalEvents, List.mem_append]
  right
  rw [pairEvents, List.mem_flatMap]
  exact ⟨a, ha, by
    rw [List.mem_flatMap]
    exact ⟨b, hb, hq⟩⟩

/-- Lifetime activity is stable across a step away from `birth` and `death+1`. -/
theorem active_succ_iff_of_not_mem_events {c : Candidate} {cs : List Candidate}
    (hc : c ∈ cs) {t : Int} (hnot : t + 1 ∉ criticalEvents cs) :
    c.Active (t + 1) ↔ c.Active t := by
  have hbirth : c.birth ≠ t + 1 := by
    intro heq
    have hm := birth_mem_criticalEvents (cs := cs) hc
    rw [heq] at hm
    exact hnot hm
  have hdeath : c.death + 1 ≠ t + 1 := by
    intro heq
    have hm := deathSucc_mem_criticalEvents (cs := cs) hc
    rw [heq] at hm
    exact hnot hm
  constructor <;> intro h <;> unfold Candidate.Active at h ⊢ <;> omega

/-- No critical event at `t+1` means every pairwise priority is unchanged. -/
theorem pair_wins_succ_iff_of_not_mem_events {a b : Candidate} {cs : List Candidate}
    (ha : a ∈ cs) (hb : b ∈ cs) {t : Int}
    (hnot : t + 1 ∉ criticalEvents cs) :
    (a.route.wins b.route (t + 1) ↔ a.route.wins b.route t) := by
  apply aff_wins_succ_iff_of_not_pairCritical
  intro hq
  exact hnot (pairCritical_mem_criticalEvents ha hb hq)

/-- **Winner-set stability away from critical events.**  This is the strict
lifetime statement: it does not claim intervality and permits re-entry at later
events. -/
theorem winner_succ_iff_of_not_mem_events {c : Candidate} {cs : List Candidate}
    {t : Int} (hnot : t + 1 ∉ criticalEvents cs) :
    Winner c cs (t + 1) ↔ Winner c cs t := by
  constructor
  · rintro ⟨hc, hact, hbeats⟩
    refine ⟨hc, (active_succ_iff_of_not_mem_events hc hnot).mp hact, ?_⟩
    intro d hd hdact
    have hdnext : d.Active (t + 1) :=
      (active_succ_iff_of_not_mem_events hd hnot).mpr hdact
    exact (pair_wins_succ_iff_of_not_mem_events hc hd hnot).mp
      (hbeats d hd hdnext)
  · rintro ⟨hc, hact, hbeats⟩
    refine ⟨hc, (active_succ_iff_of_not_mem_events hc hnot).mpr hact, ?_⟩
    intro d hd hdact
    have hdprev : d.Active t :=
      (active_succ_iff_of_not_mem_events hd hnot).mp hdact
    exact (pair_wins_succ_iff_of_not_mem_events hc hd hnot).mpr
      (hbeats d hd hdprev)

/-- Named event coverage statement: a successor change requires one of the
three advertised event types. -/
theorem winner_succ_iff_of_no_critical_event {c : Candidate} {cs : List Candidate}
    {t : Int}
    (hbirth : ∀ d ∈ cs, d.birth ≠ t + 1)
    (hdeath : ∀ d ∈ cs, d.death + 1 ≠ t + 1)
    (hcross : ∀ a ∈ cs, ∀ b ∈ cs, t + 1 ∉ pairCritical a b) :
    Winner c cs (t + 1) ↔ Winner c cs t := by
  apply winner_succ_iff_of_not_mem_events
  intro hmem
  rw [criticalEvents, List.mem_append] at hmem
  rcases hmem with hb | hp
  · rw [List.mem_flatMap] at hb
    obtain ⟨d, hd, heq⟩ := hb
    simp only [candidateEvents, List.mem_cons, List.mem_nil_iff, or_false] at heq
    rcases heq with heq | heq
    · exact hbirth d hd heq.symm
    · exact hdeath d hd heq.symm
  · rw [pairEvents, List.mem_flatMap] at hp
    obtain ⟨a, ha, hp⟩ := hp
    rw [List.mem_flatMap] at hp
    obtain ⟨b, hb, hq⟩ := hp
    exact hcross a ha b hb hq

/-- Event-list coverage: any actual successor change is forced by an event. -/
theorem winner_change_forces_event {cs : List Candidate} {t : Int}
    (hchange : ¬ SameWinnerSet cs (t + 1) t) :
    t + 1 ∈ criticalEvents cs := by
  by_cases hmem : t + 1 ∈ criticalEvents cs
  · exact hmem
  · exfalso
    apply hchange
    intro c
    exact winner_succ_iff_of_not_mem_events hmem

/-- Exact raw length of the finite event list: two lifetime events per
candidate plus all pairwise crossing windows.  Finiteness is represented
constructively by this list. -/
theorem criticalEvents_length_eq (cs : List Candidate) :
    (criticalEvents cs).length =
      (cs.map (fun c => (candidateEvents c).length)).sum +
      (cs.map (fun a => (cs.map (fun b => (pairCritical a b).length)).sum)).sum := by
  simp [criticalEvents, pairEvents, List.length_flatMap]

/-- **Exact event-scan segment theorem.**  If there is no critical event in
`(lo, t]`, then carrying the winner from the segment start `lo` gives exactly
the pointwise winner at every `t` in the segment.  This is the formal
equivalence between event scanning and direct pointwise comparison. -/
theorem critical_scan_segment_exact {cs : List Candidate} {lo hi t : Int}
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ criticalEvents cs)
    (hlo : lo ≤ t) (hhi : t ≤ hi) :
    SameWinnerSet cs t lo := by
  let n := (t - lo).toNat
  have hn : (n : Int) = t - lo := Int.toNat_of_nonneg (by omega)
  have hbound : n ≤ (hi - lo).toNat := Int.toNat_le_toNat (by omega)
  have hmain : ∀ N : Nat, N ≤ (hi - lo).toNat → SameWinnerSet cs (lo + (N : Int)) lo := by
    intro N hN
    induction N with
    | zero => simpa using sameWinnerSet_refl cs lo
    | succ N ih =>
      have ihN : SameWinnerSet cs (lo + (N : Int)) lo :=
        ih (by omega)
      have hqle : lo + (N : Int) + 1 ≤ hi := by
        have hz : 0 ≤ hi - lo := by omega
        have hle : ((N + 1 : Nat) : Int) ≤ hi - lo := (Int.le_toNat hz).mp hN
        omega
      have hqnot : lo + (N : Int) + 1 ∉ criticalEvents cs :=
        hno _ (by omega) hqle
      have hstep : SameWinnerSet cs (lo + (N : Int) + 1) (lo + (N : Int)) := by
        intro c
        simpa using winner_succ_iff_of_not_mem_events (c := c) (cs := cs) hqnot
      have hstep' : SameWinnerSet cs (lo + ((N + 1 : Nat) : Int)) (lo + (N : Int)) := by
        simpa [Int.natCast_add, Int.add_assoc] using hstep
      exact sameWinnerSet_trans hstep' ihN
  have ht : lo + (n : Int) = t := by omega
  simpa [ht] using hmain n hbound

/-- Pointwise form of the event-scan segment theorem. -/
theorem critical_scan_winner_iff {cs : List Candidate} {lo hi t : Int}
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ criticalEvents cs)
    (hlo : lo ≤ t) (hhi : t ≤ hi) (c : Candidate) :
    Winner c cs t ↔ Winner c cs lo :=
  critical_scan_segment_exact hno hlo hhi c

/-- Event-start version used by an actual scan: after processing the event at
`lo`, carrying that segment's winner is exact until just before the next event. -/
theorem critical_scan_event_winner_iff {cs : List Candidate} {lo hi t : Int}
    (_hloEvent : lo ∈ criticalEvents cs)
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ criticalEvents cs)
    (hlo : lo ≤ t) (hhi : t ≤ hi) (c : Candidate) :
    Winner c cs t ↔ Winner c cs lo :=
  critical_scan_winner_iff hno hlo hhi c

/-! ### Re-entry witness -/

/-- An always-active lower route. -/
def reentryF : Candidate :=
  ⟨⟨0, 5, 0, 0⟩, -100, 100⟩

/-- A stronger route that is alive only on `[4, 6]`. -/
def reentryG : Candidate :=
  ⟨⟨0, 9, 0, 0⟩, 4, 6⟩

def reentryCandidates : List Candidate := [reentryF, reentryG]

/-- Lifetime winners may re-enter: `reentryF` wins at `0` and `10`, loses at
`5`, and wins again later.  This is the concrete non-interval behavior that the
event-scan theorem is designed to preserve rather than suppress. -/
theorem lifetime_winner_reentry :
    Winner reentryF reentryCandidates 0 ∧
    Winner reentryF reentryCandidates 10 ∧
    ¬ Winner reentryF reentryCandidates 5 := by
  simp [Winner, reentryCandidates, reentryF, reentryG, Candidate.Active,
    AffRoute.wins, AffRoute.len, AffRoute.ep]

/-! ### Exact two-candidate characterization -/

/-- For two candidates the pointwise winner is exactly "active and either the
other is inactive or the affine priority is favorable".  This is the complete
piecewise characterization and does not impose an interval shape on lifetime. -/
theorem two_candidate_winner_iff (a b : Candidate) (t : Int) :
    Winner a [a, b] t ↔
      a.Active t ∧ (¬ b.Active t ∨ a.route.wins b.route t) := by
  constructor
  · rintro ⟨_, ha, hbeats⟩
    refine ⟨ha, ?_⟩
    by_cases hb : b.Active t
    · exact Or.inr (hbeats b (by simp) hb)
    · exact Or.inl hb
  · rintro ⟨ha, hb | hab⟩
    · refine ⟨by simp, ha, ?_⟩
      intro d hd hdact
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl
      · exact aff_wins_refl _ _
      · exact absurd hdact hb
    · refine ⟨by simp, ha, ?_⟩
      intro d hd _
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl
      · exact aff_wins_refl _ _
      · exact hab

/-- Symmetric two-candidate characterization. -/
theorem two_candidate_winner_iff_right (a b : Candidate) (t : Int) :
    Winner b [a, b] t ↔
      b.Active t ∧ (¬ a.Active t ∨ b.route.wins a.route t) := by
  constructor
  · rintro ⟨_, hb, hbeats⟩
    refine ⟨hb, ?_⟩
    by_cases ha : a.Active t
    · exact Or.inr (hbeats a (by simp) ha)
    · exact Or.inl ha
  · rintro ⟨hb, ha | hba⟩
    · refine ⟨by simp, hb, ?_⟩
      intro d hd hdact
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl
      · exact absurd hdact ha
      · exact aff_wins_refl _ _
    · refine ⟨by simp, hb, ?_⟩
      intro d hd _
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl
      · exact hba
      · exact aff_wins_refl _ _

end AffineLifetime

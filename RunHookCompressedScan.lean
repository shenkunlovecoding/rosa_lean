import HookScan
import HookDegenerate

/-!
## Connecting dense hook scans to run-compressed summaries

This file keeps the two existing developments glued at their natural seam.
`HookScan` works on a dense `Nat → Int` row, while `RunHookSummary` and
`HookDegenerate` work on a `Nat → Nat` ROSA row.  We define the restricted
window of a dense scan and identify its `P` and `A` pieces with the compressed
run summaries.  The `U` result is stated in the same endpoint-maximum form.

The final fold lemmas reduce a collection of run summaries back to the three
hook pieces and then to `HookCut.hookCut` and `CutArith.bruteKCut`.
-/

open Route
open RunRect

namespace RunHookCompressedScan

/-- Cast a natural-valued ROSA row to the integer-valued dense scan interface. -/
abbrev intRow (ell : Nat → Nat) : Nat → Int := fun e => (ell e : Int)

/-- `RspRow` is the offset-indexed `RspShape` on `z = e-c+1`. -/
theorem rspShape_of_rspRow {ell : Nat → Nat} {c d x γ : Nat}
    (hcd : c ≤ d) (h : RunHook.RspRow ell c d x γ) :
    RspSummary.RspShape (fun z => ell (c + z - 1)) x γ 1 (d - c + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz1 hzx hzn
    have hz : (c + z - 1) - c + 1 = z := by omega
    simpa [hz] using h.ramp (c + z - 1) (by omega) (by omega) (by omega)
  · intro z hz1 hzx hzn
    have hz : (c + z - 1) - c + 1 = z := by omega
    simpa [hz] using h.spike (c + z - 1) (by omega) (by omega) (by omega)
  · intro z hz1 hzx hzn
    have hz : (c + z - 1) - c + 1 = z := by omega
    simpa [hz] using h.plateau (c + z - 1) (by omega) (by omega) (by omega)

/-- Conversely, an offset-indexed `RspShape` gives a row `RspRow`. -/
theorem rspRow_of_rspShape {ell : Nat → Nat} {c d x γ : Nat}
    (hcd : c ≤ d)
    (h : RspSummary.RspShape (fun z => ell (c + z - 1)) x γ 1 (d - c + 1)) :
    RunHook.RspRow ell c d x γ := by
  refine ⟨?_, ?_, ?_⟩
  · intro e hce hed hy
    have hz : 1 ≤ e - c + 1 := by omega
    have hzn : e - c + 1 ≤ d - c + 1 := by omega
    have h1 := h.ramp (e - c + 1) hz hy hzn
    have heq : c + (e - c + 1) - 1 = e := by omega
    simpa [heq] using h1
  · intro e hce hed hy
    have hz : 1 ≤ e - c + 1 := by omega
    have hzn : e - c + 1 ≤ d - c + 1 := by omega
    have h1 := h.spike (e - c + 1) hz hy hzn
    have heq : c + (e - c + 1) - 1 = e := by omega
    simpa [heq] using h1
  · intro e hce hed hy
    have hz : 1 ≤ e - c + 1 := by omega
    have hzn : e - c + 1 ≤ d - c + 1 := by omega
    have h1 := h.plateau (e - c + 1) hz hy hzn
    have heq : c + (e - c + 1) - 1 = e := by omega
    simpa [heq] using h1

/-- The endpoint list of the inclusive run `[c,d]`. -/
def runIx (c d : Nat) : List Nat :=
  (List.range (d - c + 1)).map (fun i => c + i)

/-- Dense `P` candidates restricted to one K-run. -/
def densePRun (ell : Nat → Int) (c d : Nat) (s : Nat) : List Route :=
  (runIx c d).filter (fun e => HookScan.pEligible ell s e) |>.map
    (HookScan.routeAt ell)

/-- Dense `A` candidates restricted to a prefix `[c,E']` of one K-run. -/
def denseARun (ell : Nat → Int) (c E' : Nat) : List Route :=
  (runIx c E').filter (fun e => decide (0 < ell e)) |>.map
    (HookScan.routeAt ell)

/-- Dense `U` endpoints restricted to one K-run. -/
def denseURun (ell : Nat → Int) (c d : Nat) (s : Nat) : List Int :=
  ((runIx c d).filter (fun e => HookScan.uEligible ell s e)).map
    (fun e : Nat => (e : Int))

/-- The dense `U` maximum on one K-run. -/
def denseUMax (ell : Nat → Int) (c d : Nat) (s : Nat) : Int :=
  (denseURun ell c d s).foldr max (-1)

/-- The dense `U` maximum in `HookScan` form. -/
def uRunScan (ell : Nat → Int) (c d : Nat) (s : Nat) : Int :=
  (runIx c d).foldr
    (fun e acc => if HookScan.uEligible ell s e = true then max (e : Int) acc else acc)
    (-1)

theorem densePRun_nat_eq_pBrute (ell : Nat → Nat) (c d : Nat) (s : Nat) :
    densePRun (intRow ell) c d s = RunHook.pBrute ell c d (s : Int) := by
  unfold densePRun RunHook.pBrute runIx HookScan.pEligible HookScan.routeAt
    HookScan.delta CutArith.delta RunHook.dl intRow
  apply congrArg (List.map (fun e => (⟨(ell e : Int), (e : Int)⟩ : Route)))
  apply List.filter_congr
  intro e he
  simp [Int.natCast_pos]

theorem denseARun_nat_eq_aBrute (ell : Nat → Nat) (c E' : Nat) :
    denseARun (intRow ell) c E' = RunHook.aBrute ell c E' := by
  unfold denseARun RunHook.aBrute runIx HookScan.routeAt intRow
  apply congrArg (List.map (fun e => (⟨(ell e : Int), (e : Int)⟩ : Route)))
  apply List.filter_congr
  intro e he
  simp [Int.natCast_pos]

theorem denseUMax_eq_uRunScan (ell : Nat → Int) (c d s : Nat) :
    denseUMax ell c d s = uRunScan ell c d s := by
  unfold denseUMax denseURun uRunScan runIx
  rw [List.foldr_map, List.foldr_filter]

/-- Compressed `U` endpoint from the ramp. -/
def uRampRec (c d x : Nat) (s : Nat) : Int :=
  if 2 ≤ x ∧ (c : Int) - 1 ≤ (s : Int) then
    (min d (c + x - 2) : Int)
  else
    -1

/-- Compressed `U` endpoint from the spike. -/
def uSpikeRec (c d x γ : Nat) (s : Nat) : Int :=
  if 1 ≤ x ∧ c + x - 1 ≤ d ∧ (c : Int) - 1 - (γ : Int) ≤ (s : Int) then
    ((c + x - 1 : Nat) : Int)
  else
    -1

/-- Compressed `U` endpoint from the plateau. -/
def uPlatRec (c d x : Nat) (s : Nat) : Int :=
  if 1 ≤ x ∧ c ≤ s ∧ c + x ≤ d then
    (min d (s + x) : Int)
  else
    -1

/-- The three compressed `U` records, combined by endpoint maximum. -/
def uCompAll (c d x γ : Nat) (s : Nat) : Int :=
  max (uRampRec c d x s) (max (uSpikeRec c d x γ s) (uPlatRec c d x s))

@[simp] theorem intRow_delta (ell : Nat → Nat) (e : Nat) :
    HookScan.delta (intRow ell) e = RunHook.dl ell e := rfl

theorem denseUMax_ge_of_mem {ell : Nat → Int} {c d s e : Nat}
    (he : e ∈ runIx c d) (hel : HookScan.uEligible ell s e = true) :
    (e : Int) ≤ denseUMax ell c d s := by
  have hm : (e : Int) ∈ denseURun ell c d s := by
    unfold denseURun
    rw [List.mem_map]
    exact ⟨e, List.mem_filter.mpr ⟨he, hel⟩, rfl⟩
  unfold denseUMax
  exact CutArith.le_foldr_max _ _ hm

theorem mem_runIx {c d e : Nat} (hcd : c ≤ d) : e ∈ runIx c d ↔ c ≤ e ∧ e ≤ d := by
  unfold runIx
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    omega
  · rintro ⟨hce, hed⟩
    exact ⟨e - c, by rw [List.mem_range]; omega, by omega⟩

/-- A filtered max fold is bounded by any bound of every retained value. -/
theorem foldr_if_max_le {α : Type} (l : List α) (p : α → Bool) (f : α → Int) (b : Int)
    (hb : -1 ≤ b) (h : ∀ x, x ∈ l → p x = true → f x ≤ b) :
    l.foldr (fun x acc => if p x = true then max (f x) acc else acc) (-1) ≤ b := by
  induction l with
  | nil => simpa using hb
  | cons x xs ih =>
      rw [List.foldr_cons]
      by_cases hx : p x = true
      · rw [if_pos hx]
        exact Int.max_le.mpr ⟨h x (by simp) hx,
          ih (fun y hy hp => h y (by simp [hy]) hp)⟩
      · rw [if_neg hx]
        exact ih (fun y hy hp => h y (by simp [hy]) hp)

theorem uRampRec_le_denseUMax {ell : Nat → Nat} {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hcd : c ≤ d) (_hx : 1 ≤ x) (s : Nat) :
    uRampRec c d x s ≤ denseUMax (intRow ell) c d s := by
  unfold uRampRec
  by_cases hg : 2 ≤ x ∧ (c : Int) - 1 ≤ (s : Int)
  · rw [if_pos hg]
    let e := min d (c + x - 2)
    have he : e ∈ runIx c d := by
      unfold runIx e
      rw [List.mem_map]
      refine ⟨e - c, ?_, by omega⟩
      rw [List.mem_range]
      omega
    have hel : HookScan.uEligible (intRow ell) s e = true := by
      unfold HookScan.uEligible
      rw [decide_eq_true_eq]
      constructor
      · rw [intRow]
        have hy : e - c + 1 < x := by omega
        rw [h.ramp e (by omega) (by omega) hy]
        omega
      · rw [intRow_delta]
        have hy : e - c + 1 < x := by omega
        rw [RunHook.delta_ramp h (by omega) (by omega) hy]
        exact hg.2
    have hcast : ((min d (c + x - 2) : Nat) : Int) =
        min (d : Int) ((c : Int) + (x : Int) - 2) := by omega
    have hle : ((min d (c + x - 2) : Nat) : Int) ≤
        denseUMax (intRow ell) c d s := by
      simpa [e] using denseUMax_ge_of_mem he hel
    simpa [hcast] using hle
  · rw [if_neg hg]
    exact CutArith.neg_one_le_foldr_max _

theorem uSpikeRec_le_denseUMax {ell : Nat → Nat} {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hcd : c ≤ d) (hx : 1 ≤ x) (s : Nat) :
    uSpikeRec c d x γ s ≤ denseUMax (intRow ell) c d s := by
  unfold uSpikeRec
  by_cases hg : 1 ≤ x ∧ c + x - 1 ≤ d ∧ (c : Int) - 1 - (γ : Int) ≤ (s : Int)
  · rw [if_pos hg]
    let e := c + x - 1
    have he : e ∈ runIx c d := by
      unfold runIx e
      rw [List.mem_map]
      refine ⟨e - c, ?_, by omega⟩
      rw [List.mem_range]
      omega
    have hel : HookScan.uEligible (intRow ell) s e = true := by
      unfold HookScan.uEligible
      rw [decide_eq_true_eq]
      constructor
      · rw [intRow]
        have hy : e - c + 1 = x := by omega
        rw [h.spike e (by omega) (by omega) hy]
        omega
      · rw [intRow_delta]
        have hy : e - c + 1 = x := by omega
        rw [RunHook.delta_spike h (by omega) (by omega) hy]
        exact hg.2.2
    exact denseUMax_ge_of_mem he hel
  · rw [if_neg hg]
    exact CutArith.neg_one_le_foldr_max _

theorem uPlatRec_le_denseUMax {ell : Nat → Nat} {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hcd : c ≤ d) (hx : 1 ≤ x) (s : Nat) :
    uPlatRec c d x s ≤ denseUMax (intRow ell) c d s := by
  unfold uPlatRec
  by_cases hg : 1 ≤ x ∧ c ≤ s ∧ c + x ≤ d
  · rw [if_pos hg]
    let e := min d (s + x)
    have he : e ∈ runIx c d := by
      unfold runIx e
      rw [List.mem_map]
      refine ⟨e - c, ?_, by omega⟩
      rw [List.mem_range]
      omega
    have hel : HookScan.uEligible (intRow ell) s e = true := by
      unfold HookScan.uEligible
      rw [decide_eq_true_eq]
      constructor
      · rw [intRow]
        have hy : x < e - c + 1 := by omega
        rw [h.plateau e (by omega) (by omega) hy]
        omega
      · rw [intRow_delta]
        have hy : x < e - c + 1 := by omega
        rw [RunHook.delta_plateau h (by omega) (by omega) hy]
        omega
    have hcast : ((min d (s + x) : Nat) : Int) =
        min (d : Int) ((s : Int) + (x : Int)) := by omega
    have hle : ((min d (s + x) : Nat) : Int) ≤ denseUMax (intRow ell) c d s := by
      simpa [e] using denseUMax_ge_of_mem he hel
    simpa [hcast] using hle
  · rw [if_neg hg]
    exact CutArith.neg_one_le_foldr_max _

theorem uCompAll_ge_neg_one (c d x γ s : Nat) : -1 ≤ uCompAll c d x γ s := by
  have hr : -1 ≤ uRampRec c d x s := by
    unfold uRampRec
    split <;> omega
  unfold uCompAll
  exact Int.le_trans hr (Int.le_max_left _ _)

theorem denseU_eligible_le_uCompAll {ell : Nat → Nat} {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hcd : c ≤ d) (hx : 1 ≤ x)
    {e s : Nat} (he : e ∈ runIx c d)
    (hel : HookScan.uEligible (intRow ell) s e = true) :
    (e : Int) ≤ uCompAll c d x γ s := by
  have hce : c ≤ e := (mem_runIx hcd).mp he |>.1
  have hed : e ≤ d := (mem_runIx hcd).mp he |>.2
  have hel' : 0 < (ell e : Int) ∧
      HookScan.delta (intRow ell) e ≤ (s : Int) := by
    simpa [HookScan.uEligible] using hel
  rcases Nat.lt_trichotomy (e - c + 1) x with hy | hy | hy
  · have hx2 : 2 ≤ x := by omega
    have hpos : 0 < ell e := by
      rw [h.ramp e hce hed hy]
      omega
    have hδ : (c : Int) - 1 ≤ (s : Int) := by
      have hd := hel'.2
      rw [intRow_delta, RunHook.delta_ramp h hce hed hy] at hd
      exact hd
    have hle : (e : Int) ≤ uRampRec c d x s := by
      unfold uRampRec
      rw [if_pos ⟨hx2, hδ⟩]
      omega
    exact Int.le_trans hle (Int.le_max_left _ _)
  · have hx1 : 1 ≤ x := by omega
    have hpos : 0 < ell e := by
      rw [h.spike e hce hed hy]
      omega
    have hδ : (c : Int) - 1 - (γ : Int) ≤ (s : Int) := by
      have hd := hel'.2
      rw [intRow_delta, RunHook.delta_spike h hce hed hy] at hd
      exact hd
    have hle : (e : Int) ≤ uSpikeRec c d x γ s := by
      unfold uSpikeRec
      rw [if_pos ⟨hx1, by omega, hδ⟩]
      omega
    exact Int.le_trans hle
      (Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _))
  · have hcx : c + x ≤ e := by omega
    have hxd : c + x ≤ d := by omega
    have hcs : c ≤ s := by
      have hd := hel'.2
      have hδe : (e : Int) - (x : Int) ≤ (s : Int) := by
        rw [intRow_delta, RunHook.delta_plateau h hce hed hy] at hd
        exact hd
      omega
    have hle : (e : Int) ≤ uPlatRec c d x s := by
      unfold uPlatRec
      rw [if_pos ⟨hx, hcs, hxd⟩]
      have hd := hel'.2
      have hδe : (e : Int) - (x : Int) ≤ (s : Int) := by
        rw [intRow_delta, RunHook.delta_plateau h hce hed hy] at hd
        exact hd
      omega
    exact Int.le_trans hle
      (Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _))

theorem uRunScan_le_uCompAll {ell : Nat → Nat} {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hcd : c ≤ d) (hx : 1 ≤ x) (s : Nat) :
    uRunScan (intRow ell) c d s ≤ uCompAll c d x γ s := by
  unfold uRunScan
  apply foldr_if_max_le
  · exact uCompAll_ge_neg_one c d x γ s
  · intro e he hel
    exact denseU_eligible_le_uCompAll h hcd hx he hel

theorem uCompAll_le_denseUMax {ell : Nat → Nat} {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hcd : c ≤ d) (hx : 1 ≤ x) (s : Nat) :
    uCompAll c d x γ s ≤ denseUMax (intRow ell) c d s := by
  unfold uCompAll
  exact Int.max_le.mpr
    ⟨uRampRec_le_denseUMax h hcd hx s,
     Int.max_le.mpr ⟨uSpikeRec_le_denseUMax h hcd hx s,
       uPlatRec_le_denseUMax h hcd hx s⟩⟩

/-- The compressed `U` records are exactly the dense run-window maximum. -/
theorem U_run_eq_dense (ell : Nat → Nat) {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hcd : c ≤ d) (hx : 1 ≤ x) (s : Nat) :
    denseUMax (intRow ell) c d s = uCompAll c d x γ s := by
  apply Int.le_antisymm
  · rw [denseUMax_eq_uRunScan]
    exact uRunScan_le_uCompAll h hcd hx s
  · exact uCompAll_le_denseUMax h hcd hx s

/-- The `P` summary of `HookDegenerate` is exactly the dense `P` window. -/
theorem P_run_eq_dense (ell : Nat → Nat) {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hcd : c ≤ d) (s : Nat) :
    rmaxList (densePRun (intRow ell) c d s) =
      rmaxList (RunHook.pCompAll c d x γ (s : Int)) := by
  rw [densePRun_nat_eq_pBrute]
  exact RunHook.P_run_eq_all h hcd (s : Int)

/-- The `A` summary of `HookDegenerate` is exactly the dense `A` window. -/
theorem A_run_eq_dense (ell : Nat → Nat) {c d x γ : Nat}
    (h : RunHook.RspRow ell c d x γ) (hx : 1 ≤ x)
    {E' : Nat} (hcE : c ≤ E') (hEd : E' ≤ d) :
    rmaxList (denseARun (intRow ell) c E') =
      RunHook.aComp ell c x γ E' := by
  rw [denseARun_nat_eq_aBrute]
  exact RunHook.A_run_eq_all h hx hcE hEd


/-- `P` compressed records from an offset `RspShape`. -/
theorem P_run_eq_dense_of_rspShape (ell : Nat → Nat) {c d x γ : Nat}
    (hcd : c ≤ d)
    (h : RspSummary.RspShape (fun z => ell (c + z - 1)) x γ 1 (d - c + 1))
    (s : Nat) :
    rmaxList (densePRun (intRow ell) c d s) =
      rmaxList (RunHook.pCompAll c d x γ (s : Int)) :=
  P_run_eq_dense ell (rspRow_of_rspShape hcd h) hcd s

/-- `U` compressed records from an offset `RspShape`. -/
theorem U_run_eq_dense_of_rspShape (ell : Nat → Nat) {c d x γ : Nat}
    (hcd : c ≤ d) (hx : 1 ≤ x)
    (h : RspSummary.RspShape (fun z => ell (c + z - 1)) x γ 1 (d - c + 1))
    (s : Nat) :
    denseUMax (intRow ell) c d s = uCompAll c d x γ s :=
  U_run_eq_dense ell (rspRow_of_rspShape hcd h) hcd hx s

/-- `A` compressed records from an offset `RspShape`. -/
theorem A_run_eq_dense_of_rspShape (ell : Nat → Nat) {c d x γ : Nat}
    (hcd : c ≤ d) (hx : 1 ≤ x)
    (h : RspSummary.RspShape (fun z => ell (c + z - 1)) x γ 1 (d - c + 1))
    {E' : Nat} (hcE : c ≤ E') (hEd : E' ≤ d) :
    rmaxList (denseARun (intRow ell) c E') =
      RunHook.aComp ell c x γ E' :=
  A_run_eq_dense ell (rspRow_of_rspShape hcd h) hx hcE hEd

/-- Turn a compressed endpoint maximum into the `R(s)` ramp/plateau route. -/
def rFromU (U : Int) (s : Nat) : Route :=
  if (s : Int) < U then CutArith.mk (U - (s : Int)) U else unmatched

/-- Fold the three hook pieces after `A`, `P`, and `U` summaries have been
computed (possibly by folding per-run summaries). -/
def foldedHookCut (A P : Route) (U : Int) (s : Nat) : Route :=
  rmax A (rmax P (rFromU U s))

theorem rFromU_uScan (ell : Nat → Int) (t s : Nat) :
    rFromU (HookScan.uScan ell t s) s = HookScan.rScan ell t s := by
  rfl

/-- The folded compressed hook is the dense scan cut once the three dense
global summaries have been supplied. -/
theorem foldedHookCut_eq_scanCut {ell : Nat → Int} {t s : Nat} {A P : Route} {U : Int}
    (hA : A = HookScan.aScan ell t s)
    (hP : P = HookScan.pScan ell t s)
    (hU : U = HookScan.uScan ell t s) :
    foldedHookCut A P U s = HookScan.scanCut ell t s := by
  subst hA
  subst hP
  subst hU
  unfold foldedHookCut HookScan.scanCut
  rw [rFromU_uScan]

/-- Folded compressed summaries have exactly the `HookCut` semantics. -/
theorem foldedHookCut_eq_hookCut {ell : Nat → Int} {t s : Nat} {A P : Route} {U : Int}
    (hA : A = HookScan.aScan ell t s)
    (hP : P = HookScan.pScan ell t s)
    (hU : U = HookScan.uScan ell t s) :
    foldedHookCut A P U s = HookCut.hookCut ell t s := by
  rw [foldedHookCut_eq_scanCut hA hP hU]
  exact HookScan.scanCut_eq_hookCut ell t s

/-- The same folded summaries have exactly the brute K-cut semantics. -/
theorem foldedHookCut_eq_bruteKCut {ell : Nat → Int} {t s : Nat} {A P : Route} {U : Int}
    (hA : A = HookScan.aScan ell t s)
    (hP : P = HookScan.pScan ell t s)
    (hU : U = HookScan.uScan ell t s) :
    foldedHookCut A P U s = CutArith.bruteKCut ell t s := by
  rw [foldedHookCut_eq_scanCut hA hP hU]
  exact HookScan.scanCut_eq_bruteKCut ell t s

/-- Fold route summaries over an arbitrary list of runs. -/
def foldRunRoutes {α : Type} (f : α → Route) (runs : List α) : Route :=
  rmaxList (runs.map f)

/-- Fold endpoint maxima over an arbitrary list of runs. -/
def foldRunEndpoints {α : Type} (f : α → Int) (runs : List α) : Int :=
  (runs.map f).foldr max (-1)

/-- Folding per-run `A`, `P`, and `U` summaries gives `HookCut` once the three
folds have been identified with the dense scans. -/
theorem foldedRunSummaries_eq_hookCut {α : Type} {ell : Nat → Int} {t s : Nat}
    (runs : List α) (A P : α → Route) (U : α → Int)
    (hA : foldRunRoutes A runs = HookScan.aScan ell t s)
    (hP : foldRunRoutes P runs = HookScan.pScan ell t s)
    (hU : foldRunEndpoints U runs = HookScan.uScan ell t s) :
    foldedHookCut (foldRunRoutes A runs) (foldRunRoutes P runs)
      (foldRunEndpoints U runs) s = HookCut.hookCut ell t s :=
  foldedHookCut_eq_hookCut hA hP hU

/-- Brute-cut form of `foldedRunSummaries_eq_hookCut`. -/
theorem foldedRunSummaries_eq_bruteKCut {α : Type} {ell : Nat → Int} {t s : Nat}
    (runs : List α) (A P : α → Route) (U : α → Int)
    (hA : foldRunRoutes A runs = HookScan.aScan ell t s)
    (hP : foldRunRoutes P runs = HookScan.pScan ell t s)
    (hU : foldRunEndpoints U runs = HookScan.uScan ell t s) :
    foldedHookCut (foldRunRoutes A runs) (foldRunRoutes P runs)
      (foldRunEndpoints U runs) s = CutArith.bruteKCut ell t s :=
  foldedHookCut_eq_bruteKCut hA hP hU

end RunHookCompressedScan

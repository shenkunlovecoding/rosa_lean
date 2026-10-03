import RunHookCompressedScan

/-!
## Ordered run coverage and Hook fold assembly

The one-run lemmas in `RunHookCompressedScan` reduce each compressed summary to
a dense window.  This file glues those windows over an ordered, adjacent list of
runs.  A run is represented as a half-open interval `[lo, hi)`; the `RspRow`
proof concerns the inclusive dense interval `[lo, hi-1]`.  The last run of a
list may therefore be a partial prefix of a longer physical run.

The main results fold `RunHook.pCompAll`, `RunHookCompressedScan.uCompAll`, and
`RunHook.aComp` over that list and identify the results with the corresponding
global dense scans.
-/

open Route

namespace RunHookCoverage

open RunHookCompressedScan

/-- A run window `[lo, hi)` with an RSP shape on its inclusive endpoint range
`[lo, hi-1]`.  `x_pos` is the ROSA-domain condition `1 ≤ x`; it is needed by the
`U` and `A` summaries. -/
structure RunBlock (ell : Nat → Nat) where
  lo : Nat
  hi : Nat
  x : Nat
  gamma : Nat
  nonempty : lo < hi
  x_pos : 1 ≤ x
  rsp : RunHook.RspRow ell lo (hi - 1) x gamma

namespace RunBlock

/-- Inclusive right endpoint of the window. -/
def d {ell : Nat → Nat} (R : RunBlock ell) : Nat := R.hi - 1

theorem lo_le_d {ell : Nat → Nat} (R : RunBlock ell) : R.lo ≤ R.d := by
  unfold d
  exact Nat.le_sub_one_of_lt R.nonempty

theorem d_lt_hi {ell : Nat → Nat} (R : RunBlock ell) : R.d < R.hi := by
  unfold RunBlock.d
  have hpos : 0 < R.hi := Nat.lt_of_le_of_lt (Nat.zero_le R.lo) R.nonempty
  omega

/-- Restrict a run to a partial prefix, retaining its `RspRow` proof. -/
def restrict {ell : Nat → Nat} (R : RunBlock ell) (hi' : Nat)
    (hlo : R.lo < hi') (hhi : hi' ≤ R.hi) : RunBlock ell where
  lo := R.lo
  hi := hi'
  x := R.x
  gamma := R.gamma
  nonempty := hlo
  x_pos := R.x_pos
  rsp := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he her hlt
      exact R.rsp.ramp e he (by omega) hlt
    · intro e he her heq
      exact R.rsp.spike e he (by omega) heq
    · intro e he her hgt
      exact R.rsp.plateau e he (by omega) hgt

end RunBlock

/-- Ordered adjacent coverage of `[lo, hi)` by run windows. -/
inductive OrderedCoverage (ell : Nat → Nat) : Nat → Nat → List (RunBlock ell) → Prop
  | nil {lo} : OrderedCoverage ell lo lo []
  | cons {lo hi} (R : RunBlock ell) (rest : List (RunBlock ell))
      (hlo : R.lo = lo)
      (hrest : OrderedCoverage ell R.hi hi rest) :
      OrderedCoverage ell lo hi (R :: rest)

namespace OrderedCoverage

theorem le {ell : Nat → Nat} {lo hi : Nat} {runs : List (RunBlock ell)}
    (h : OrderedCoverage ell lo hi runs) : lo ≤ hi := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons R rest hlo hrest ih =>
      rename_i lo' hi'
      rw [← hlo]
      exact Nat.le_trans (Nat.le_of_lt R.nonempty) ih

/-- The first run of a coverage starting at zero is the initial run `c = 0`. -/
theorem head_lo_zero {ell : Nat → Nat} {hi : Nat} {R : RunBlock ell}
    {rest : List (RunBlock ell)}
    (h : OrderedCoverage ell 0 hi (R :: rest)) : R.lo = 0 := by
  cases h with
  | cons _ _ hlo _ => exact hlo

/-- Append two adjacent coverages. -/
theorem append {ell : Nat → Nat} {lo mid hi : Nat}
    {runs₁ runs₂ : List (RunBlock ell)}
    (h₁ : OrderedCoverage ell lo mid runs₁)
    (h₂ : OrderedCoverage ell mid hi runs₂) :
    OrderedCoverage ell lo hi (runs₁ ++ runs₂) := by
  induction h₁ generalizing hi with
  | nil => simpa using h₂
  | cons R rest hlo hrest ih =>
      simp only [List.cons_append]
      exact OrderedCoverage.cons R (rest ++ runs₂) hlo (ih h₂)

/-- Append one final run; this is the complete-old-runs plus current-prefix
assembly step. -/
theorem snoc {ell : Nat → Nat} {lo hi t : Nat} {runs : List (RunBlock ell)}
    (h : OrderedCoverage ell lo hi runs) (R : RunBlock ell)
    (hlo : R.lo = hi) (hhi : R.hi = t) :
    OrderedCoverage ell lo t (runs ++ [R]) := by
  have htail : OrderedCoverage ell hi t [R] := by
    refine OrderedCoverage.cons R [] hlo ?_
    simpa [hhi] using (OrderedCoverage.nil (ell := ell) (lo := t))
  exact h.append htail

/-- A coverage of the empty prefix is necessarily the empty run list. -/
theorem zero_eq_nil {ell : Nat → Nat} {runs : List (RunBlock ell)}
    (h : OrderedCoverage ell 0 0 runs) : runs = [] := by
  cases h with
  | nil => rfl
  | cons R rest hlo hrest =>
      exfalso
      have hle := le hrest
      have hlt := R.nonempty
      rw [hlo] at hlt
      omega

end OrderedCoverage

/-- Half-open endpoint list `[lo, hi)`. -/
def runIxHalf (lo hi : Nat) : List Nat := List.range' lo (hi - lo)

theorem runIx_eq_half {c d : Nat} (hcd : c ≤ d) :
    runIx c d = runIxHalf c (d + 1) := by
  unfold runIx runIxHalf
  rw [List.range'_eq_map_range]
  apply congrArg (List.map (fun x => c + x))
  rw [Nat.succ_sub hcd]

theorem runIx_block_eq {ell : Nat → Nat} (R : RunBlock ell) :
    runIx R.lo R.d = runIxHalf R.lo R.hi := by
  unfold RunBlock.d
  have hlt : 0 < R.hi := Nat.lt_of_le_of_lt (Nat.zero_le R.lo) R.nonempty
  have hle : R.lo ≤ R.hi - 1 := Nat.le_sub_one_of_lt R.nonempty
  have h := runIx_eq_half (c := R.lo) (d := R.hi - 1) hle
  simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hlt)] using h

theorem range'_split {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
  let m := b - a
  let n := c - b
  have hm : m = b - a := rfl
  have hn : n = c - b := rfl
  have hstart : a + m = b := by
    dsimp [m]
    exact Nat.add_sub_of_le hab
  have hlen : m + n = c - a := by
    dsimp [m, n]
    omega
  rw [← hm, ← hn, ← hstart, ← hlen]
  simp

/-! ### Dense interval forms -/

/-- Dense `P` candidates over `[lo, hi)`. -/
def densePInterval (ell : Nat → Int) (lo hi s : Nat) : List Route :=
  ((runIxHalf lo hi).filter (fun e => HookScan.pEligible ell s e)).map
    (HookScan.routeAt ell)

/-- Dense eligible `U` endpoints over `[lo, hi)`. -/
def denseUInterval (ell : Nat → Int) (lo hi s : Nat) : List Int :=
  ((runIxHalf lo hi).filter (fun e => HookScan.uEligible ell s e)).map
    (fun e => Int.ofNat e)

/-- Dense positive `A` candidates over `[lo, hi)`. -/
def denseAInterval (ell : Nat → Int) (lo hi : Nat) : List Route :=
  ((runIxHalf lo hi).filter (fun e => decide (0 < ell e))).map
    (HookScan.routeAt ell)

theorem densePInterval_split (ell : Nat → Int) {a b c s : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) :
    densePInterval ell a b s ++ densePInterval ell b c s =
      densePInterval ell a c s := by
  unfold densePInterval runIxHalf
  rw [← range'_split hab hbc]
  rw [List.filter_append, List.map_append]

theorem denseUInterval_split (ell : Nat → Int) {a b c s : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) :
    denseUInterval ell a b s ++ denseUInterval ell b c s =
      denseUInterval ell a c s := by
  unfold denseUInterval runIxHalf
  rw [← range'_split hab hbc]
  rw [List.filter_append, List.map_append]

theorem denseAInterval_split (ell : Nat → Int) {a b c : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) :
    denseAInterval ell a b ++ denseAInterval ell b c =
      denseAInterval ell a c := by
  unfold denseAInterval runIxHalf
  rw [← range'_split hab hbc]
  rw [List.filter_append, List.map_append]

/-! ### Validity and fold lemmas -/

theorem valid_densePInterval (ell : Nat → Int) (lo hi s : Nat) :
    ∀ r ∈ densePInterval ell lo hi s, Valid r := by
  intro r hr
  unfold densePInterval at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, rfl⟩ := hr
  rw [List.mem_filter] at he
  simp only [HookScan.pEligible, decide_eq_true_eq] at he
  exact HookScan.valid_routeAt ell e he.2.1

theorem valid_denseAInterval (ell : Nat → Int) (lo hi : Nat) :
    ∀ r ∈ denseAInterval ell lo hi, Valid r := by
  intro r hr
  unfold denseAInterval at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, rfl⟩ := hr
  rw [List.mem_filter] at he
  simp only [decide_eq_true_eq] at he
  exact HookScan.valid_routeAt ell e he.2

theorem mem_denseAInterval {ell : Nat → Int} {lo hi : Nat} {r : Route} :
    r ∈ denseAInterval ell lo hi ↔
      ∃ e, lo ≤ e ∧ e < hi ∧ 0 < ell e ∧ r = HookScan.routeAt ell e := by
  unfold denseAInterval runIxHalf
  rw [List.mem_map]
  constructor
  · rintro ⟨e', he', heq⟩
    rw [List.mem_filter] at he'
    simp only [decide_eq_true_eq] at he'
    rw [List.mem_range'] at he'
    obtain ⟨k, hk, hk_eq⟩ := he'.1
    exact ⟨e', by omega, by omega, he'.2, heq.symm⟩
  · rintro ⟨e, hlo, hhi, hpos, rfl⟩
    refine ⟨e, ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨?_, by simpa using hpos⟩
    rw [List.mem_range']
    exact ⟨e - lo, by omega, by omega⟩

theorem foldr_max_append (l₁ l₂ : List Int) :
    (l₁ ++ l₂).foldr max (-1) =
      max (l₁.foldr max (-1)) (l₂.foldr max (-1)) := by
  induction l₁ with
  | nil =>
      simp [Int.max_eq_right (CutArith.neg_one_le_foldr_max l₂)]
  | cons x xs ih =>
      rw [List.cons_append, List.foldr_cons, ih, List.foldr_cons]
      rw [Int.max_assoc]

theorem foldRunRoutes_cons {α : Type} (f : α → Route) (R : α) (rest : List α) :
    foldRunRoutes f (R :: rest) = rmax (f R) (foldRunRoutes f rest) := by
  rfl

theorem foldRunEndpoints_cons {α : Type} (f : α → Int) (R : α) (rest : List α) :
    foldRunEndpoints f (R :: rest) = max (f R) (foldRunEndpoints f rest) := by
  rfl

/-! ### Per-run summaries in half-open form -/

def runPWindow {ell : Nat → Nat} (R : RunBlock ell) (s : Nat) : List Route :=
  densePInterval (intRow ell) R.lo R.hi s

def runUWindow {ell : Nat → Nat} (R : RunBlock ell) (s : Nat) : List Int :=
  denseUInterval (intRow ell) R.lo R.hi s

def runAWindow {ell : Nat → Nat} (R : RunBlock ell) : List Route :=
  denseAInterval (intRow ell) R.lo R.hi

theorem runPWindow_rmax {ell : Nat → Nat} (R : RunBlock ell) (s : Nat) :
    rmaxList (runPWindow R s) =
      rmaxList (RunHook.pCompAll R.lo R.d R.x R.gamma (s : Int)) := by
  unfold runPWindow densePInterval RunBlock.d
  rw [← runIx_block_eq R]
  exact P_run_eq_dense ell R.rsp R.lo_le_d s

theorem runUWindow_fold {ell : Nat → Nat} (R : RunBlock ell) (s : Nat) :
    (runUWindow R s).foldr max (-1) =
      uCompAll R.lo R.d R.x R.gamma s := by
  unfold runUWindow denseUInterval RunBlock.d
  rw [← runIx_block_eq R]
  exact U_run_eq_dense ell R.rsp R.lo_le_d R.x_pos s

theorem runAWindow_rmax {ell : Nat → Nat} (R : RunBlock ell) :
    rmaxList (runAWindow R) =
      RunHook.aComp ell R.lo R.x R.gamma R.d := by
  unfold runAWindow denseAInterval RunBlock.d
  rw [← runIx_block_eq R]
  exact A_run_eq_dense ell R.rsp R.x_pos R.lo_le_d (Nat.le_refl _)

/-! ### Ordered folds -/

def foldP {ell : Nat → Nat} (runs : List (RunBlock ell)) (s : Nat) : Route :=
  foldRunRoutes
    (fun R => rmaxList (RunHook.pCompAll R.lo R.d R.x R.gamma (s : Int))) runs

def foldU {ell : Nat → Nat} (runs : List (RunBlock ell)) (s : Nat) : Int :=
  foldRunEndpoints (fun R => uCompAll R.lo R.d R.x R.gamma s) runs

def foldA {ell : Nat → Nat} (runs : List (RunBlock ell)) : Route :=
  foldRunRoutes (fun R => RunHook.aComp ell R.lo R.x R.gamma R.d) runs

theorem foldP_eq_denseP {ell : Nat → Nat} :
    ∀ {lo hi : Nat} {runs : List (RunBlock ell)},
    OrderedCoverage ell lo hi runs →
    foldP runs s = rmaxList (densePInterval (intRow ell) lo hi s) := by
  intro lo hi runs h
  induction h with
  | nil =>
      simp [foldP, foldRunRoutes, densePInterval, runIxHalf]
  | cons R rest hlo hrest ih =>
      rename_i lo' hi'
      rw [← hlo]
      unfold foldP at ih ⊢
      rw [foldRunRoutes_cons, ih]
      rw [← runPWindow_rmax R s]
      change rmax (rmaxList (runPWindow R s))
          (rmaxList (densePInterval (intRow ell) R.hi hi' s)) =
        rmaxList (densePInterval (intRow ell) R.lo hi' s)
      rw [← densePInterval_split (intRow ell) (Nat.le_of_lt R.nonempty) (OrderedCoverage.le hrest)]
      rw [rmaxList_append
        (densePInterval (intRow ell) R.lo R.hi s)
        (densePInterval (intRow ell) R.hi hi' s)
        (valid_densePInterval (intRow ell) R.hi hi' s)]
      rfl

theorem foldU_eq_denseU {ell : Nat → Nat} :
    ∀ {lo hi : Nat} {runs : List (RunBlock ell)},
    OrderedCoverage ell lo hi runs →
    foldU runs s =
      (denseUInterval (intRow ell) lo hi s).foldr max (-1) := by
  intro lo hi runs h
  induction h with
  | nil =>
      simp [foldU, foldRunEndpoints, denseUInterval, runIxHalf]
  | cons R rest hlo hrest ih =>
      rename_i lo' hi'
      rw [← hlo]
      unfold foldU at ih ⊢
      rw [foldRunEndpoints_cons, ih]
      rw [← runUWindow_fold R s]
      change max ((runUWindow R s).foldr max (-1))
          ((denseUInterval (intRow ell) R.hi hi' s).foldr max (-1)) =
        (denseUInterval (intRow ell) R.lo hi' s).foldr max (-1)
      rw [← denseUInterval_split (intRow ell) (Nat.le_of_lt R.nonempty) (OrderedCoverage.le hrest)]
      rw [foldr_max_append]
      rfl

theorem foldA_eq_denseA {ell : Nat → Nat} :
    ∀ {lo hi : Nat} {runs : List (RunBlock ell)},
    OrderedCoverage ell lo hi runs →
    foldA runs = rmaxList (denseAInterval (intRow ell) lo hi) := by
  intro lo hi runs h
  induction h with
  | nil =>
      simp [foldA, foldRunRoutes, denseAInterval, runIxHalf]
  | cons R rest hlo hrest ih =>
      rename_i lo' hi'
      rw [← hlo]
      unfold foldA at ih ⊢
      rw [foldRunRoutes_cons, ih]
      rw [← runAWindow_rmax R]
      change rmax (rmaxList (runAWindow R))
          (rmaxList (denseAInterval (intRow ell) R.hi hi')) =
        rmaxList (denseAInterval (intRow ell) R.lo hi')
      rw [← denseAInterval_split (intRow ell) (Nat.le_of_lt R.nonempty) (OrderedCoverage.le hrest)]
      rw [rmaxList_append
        (denseAInterval (intRow ell) R.lo R.hi)
        (denseAInterval (intRow ell) R.hi hi')
        (valid_denseAInterval (intRow ell) R.hi hi')]
      rfl

/-! ### Global dense scans -/

theorem pScan_eq_densePInterval (ell : Nat → Int) (t s : Nat) :
    HookScan.pScan ell t s = rmaxList (densePInterval ell 0 t s) := by
  unfold HookScan.pScan densePInterval runIxHalf
  rw [List.range_eq_range']
  rw [HookScan.rmaxList_eq_foldr, List.foldr_map, List.foldr_filter]
  simp

theorem uScan_eq_denseUInterval (ell : Nat → Int) (t s : Nat) :
    HookScan.uScan ell t s =
      (denseUInterval ell 0 t s).foldr max (-1) := by
  unfold HookScan.uScan denseUInterval runIxHalf
  rw [List.range_eq_range']
  rw [List.foldr_map, List.foldr_filter]
  simp

theorem aScan_eq_denseAInterval (ell : Nat → Int) {t s : Nat} (hst : s ≤ t) :
    HookScan.aScan ell t s = rmaxList (denseAInterval ell 0 s) := by
  rw [HookScan.aScan_eq_ApartC]
  unfold HookCut.ApartC
  apply rle_antisymm
  · apply rmaxList_lub
    · exact valid_rmaxList _ (valid_denseAInterval ell 0 s)
    · intro r hr
      unfold CutArith.apartList at hr
      rw [List.mem_map] at hr
      obtain ⟨e, he, rfl⟩ := hr
      rw [List.mem_filter] at he
      simp only [decide_eq_true_eq] at he
      apply rle_rmaxList
      rw [mem_denseAInterval]
      exact ⟨e, by omega, he.2.1, he.2.2, rfl⟩
  · apply rmaxList_lub
    · exact valid_rmaxList _ (HookCut.valid_apartList ell t s)
    · intro r hr
      rw [mem_denseAInterval] at hr
      obtain ⟨e, hlo, hhi, hpos, rfl⟩ := hr
      apply rle_rmaxList
      have hmem : (⟨ell e, (e : Int)⟩ : Route) ∈ CutArith.apartList ell t s := by
        rw [CutArith.mem_apartList]
        exact ⟨by omega, hhi, hpos⟩
      simpa [HookScan.routeAt] using hmem

/-! ### Main assembly theorems -/

/-- Fold per-run all-case `P` summaries over an ordered coverage of `[0,t)`;
the result is the global `HookScan.pScan`. -/
theorem fold_pCompAll_eq_pScan {ell : Nat → Nat} {t s : Nat}
    {runs : List (RunBlock ell)}
    (hcover : OrderedCoverage ell 0 t runs) :
    foldP runs s = HookScan.pScan (intRow ell) t s := by
  rw [pScan_eq_densePInterval]
  exact foldP_eq_denseP hcover

/-- Fold per-run compressed `U` endpoint summaries over an ordered coverage of
`[0,t)`; the result is the global `HookScan.uScan`. -/
theorem fold_uCompAll_eq_uScan {ell : Nat → Nat} {t s : Nat}
    {runs : List (RunBlock ell)}
    (hcover : OrderedCoverage ell 0 t runs) :
    foldU runs s = HookScan.uScan (intRow ell) t s := by
  rw [uScan_eq_denseUInterval]
  exact foldU_eq_denseU hcover

/-- Fold per-run `A` summaries over an ordered coverage of the prefix `[0,s)`.
No run is needed when `s = 0`; a final partial run may end exactly at `s`.
The owner index is assumed inside the dense row, `s ≤ t`. -/
theorem fold_aComp_eq_aScan {ell : Nat → Nat} {t s : Nat}
    {runs : List (RunBlock ell)}
    (hcover : OrderedCoverage ell 0 s runs) (hst : s ≤ t) :
    foldA runs = HookScan.aScan (intRow ell) t s := by
  rw [aScan_eq_denseAInterval (intRow ell) hst]
  exact foldA_eq_denseA hcover

/-- End-to-end Hook assembly: `P/U` use the ordered coverage of `[0,t)`,
while `A` uses the ordered prefix coverage of `[0,s)`. -/
theorem foldedHookCut_of_orderedCoverage {ell : Nat → Nat} {t s : Nat}
    {runsPU runsA : List (RunBlock ell)}
    (hPU : OrderedCoverage ell 0 t runsPU)
    (hA : OrderedCoverage ell 0 s runsA) (hst : s ≤ t) :
    foldedHookCut (foldA runsA) (foldP runsPU s) (foldU runsPU s) s =
      HookCut.hookCut (intRow ell) t s := by
  apply foldedHookCut_eq_hookCut
  · exact fold_aComp_eq_aScan hA hst
  · exact fold_pCompAll_eq_pScan hPU
  · exact fold_uCompAll_eq_uScan hPU

end RunHookCoverage

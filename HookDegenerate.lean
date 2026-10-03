import Std
import RunHookSummary
import RspSummary

/-!
## Phase E — degenerate run-hook summaries

This file closes the edge cases of `RunHookSummary` without changing the
existing development.  The semantically relevant row offset is `x = t-a+1`,
so `1 ≤ x`; the old non-degenerate theorems additionally assumed `2 ≤ x` and
`c+x ≤ d`, which made the ramp, spike and plateau all non-empty.

The exact all-case `P` summary uses `pCompAll`.  It keeps a ramp record only
when the ramp is non-empty, keeps the spike/plateau records only when their
displayed endpoints lie inside `[c,d]`, and truncates the ramp record at `d`
on a short run.  Thus it does not introduce a record for an absent phase.
The `U` theorem below states the unconditional pointwise criterion on the
plateau and adds the latest-endpoint witness only when the plateau is
non-empty.  The `A` theorem drops `c+x ≤ d` and weakens `2 ≤ x` to `1 ≤ x`;
its proof also covers the initial run `c = 0`.

`x = 0` is outside the ROSA offset domain.  The exact `P` summary is stated
for all naturals anyway; the old `A`/`U` statements are recovered for `x ≥ 1`.
-/

open Route RunRect

namespace RunHook

/-- All-case ramp record: empty ramp is `unmatched`; a short ramp is truncated
at the last endpoint `d`. -/
def rampRecAll (c d x : Nat) (s : Int) : Route :=
  if 2 ≤ x then
    let e := min d (c + x - 2)
    if (c : Int) - 1 > s then
      (⟨((e - c + 1 : Nat) : Int), (e : Int)⟩ : Route)
    else
      unmatched
  else
    unmatched

/-- All-case spike record: absent spike is `unmatched`. -/
def spikeRecAll (c d x γ : Nat) (s : Int) : Route :=
  if 1 ≤ x ∧ c + x - 1 ≤ d then spikeRec c x γ s else unmatched

/-- All-case plateau record: absent plateau is `unmatched`. -/
def platRecAll (c d x : Nat) (s : Int) : Route :=
  if 1 ≤ x ∧ c + x ≤ d then platRec d x s else unmatched

/-- Exact finite run summary with all empty phases removed/truncated. -/
def pCompAll (c d x γ : Nat) (s : Int) : List Route :=
  [rampRecAll c d x s, spikeRecAll c d x γ s, platRecAll c d x s]

theorem valid_rampRecAll (c d x : Nat) (s : Int) :
    Valid (rampRecAll c d x s) := by
  unfold rampRecAll
  by_cases hx : 2 ≤ x
  · rw [if_pos hx]
    by_cases hs : (c : Int) - 1 > s
    · rw [if_pos hs]
      exact CutArith.valid_pair _ _ (by omega) (by omega)
    · rw [if_neg hs]
      exact valid_unmatched
  · rw [if_neg hx]
    exact valid_unmatched

theorem valid_spikeRecAll (c d x γ : Nat) (s : Int) :
    Valid (spikeRecAll c d x γ s) := by
  unfold spikeRecAll
  by_cases hp : 1 ≤ x ∧ c + x - 1 ≤ d
  · rw [if_pos hp]
    unfold spikeRec
    by_cases hs : (c : Int) - 1 - (γ : Int) > s
    · rw [if_pos hs]
      exact CutArith.valid_pair _ _ (by omega) (by omega)
    · rw [if_neg hs]
      exact valid_unmatched
  · rw [if_neg hp]
    exact valid_unmatched

theorem valid_platRecAll (c d x : Nat) (s : Int) :
    Valid (platRecAll c d x s) := by
  unfold platRecAll
  by_cases hp : 1 ≤ x ∧ c + x ≤ d
  · rw [if_pos hp]
    unfold platRec
    by_cases hs : (d : Int) - (x : Int) > s
    · rw [if_pos hs]
      exact CutArith.valid_pair _ _ (by omega) (by omega)
    · rw [if_neg hs]
      exact valid_unmatched
  · rw [if_neg hp]
    exact valid_unmatched

theorem valid_pCompAll (c d x γ : Nat) (s : Int) :
    ∀ r ∈ pCompAll c d x γ s, Valid r := by
  intro r hr
  simp only [pCompAll, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact valid_rampRecAll c d x s
  · exact valid_spikeRecAll c d x γ s
  · exact valid_platRecAll c d x s

/-- Exact all-case E1 summary.  No non-emptiness assumptions are needed. -/
theorem P_run_eq_all {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    (hcd : c ≤ d) (s : Int) :
    rmaxList (pBrute ell c d s) = rmaxList (pCompAll c d x γ s) := by
  have hvc : Valid (rmaxList (pCompAll c d x γ s)) :=
    valid_rmaxList _ (valid_pCompAll c d x γ s)
  have hvb : Valid (rmaxList (pBrute ell c d s)) :=
    valid_rmaxList _ (valid_pBrute ell c d s)
  apply rle_antisymm
  · apply rmaxList_lub
    · exact hvc
    · intro r hr
      rw [mem_pBrute hcd] at hr
      obtain ⟨e, hce, hed, hpos, hlt, rfl⟩ := hr
      rcases Nat.lt_trichotomy (e - c + 1) x with hy | hy | hy
      · have hx2 : 2 ≤ x := by omega
        have hde : dl ell e = (c : Int) - 1 := delta_ramp h hce hed hy
        have hramp : (c : Int) - 1 > s := by rw [← hde]; exact hlt
        have hemin : e ≤ min d (c + x - 2) := by omega
        have hmem : rampRecAll c d x s ∈ pCompAll c d x γ s := by simp [pCompAll]
        refine rle_trans _ _ _ ?_ (rle_rmaxList _ _ hmem)
        unfold rampRecAll
        rw [if_pos hx2, if_pos hramp]
        unfold rle
        dsimp only
        rw [h.ramp e hce hed hy]
        omega
      · have hx1 : 1 ≤ x := by omega
        have hspike_present : c + x - 1 ≤ d := by omega
        have hde : dl ell e = (c : Int) - 1 - (γ : Int) := delta_spike h hce hed hy
        have hsp : (c : Int) - 1 - (γ : Int) > s := by rw [← hde]; exact hlt
        have hmem : spikeRecAll c d x γ s ∈ pCompAll c d x γ s := by simp [pCompAll]
        refine rle_trans _ _ _ ?_ (rle_rmaxList _ _ hmem)
        unfold spikeRecAll
        rw [if_pos ⟨hx1, hspike_present⟩]
        unfold spikeRec
        rw [if_pos hsp]
        unfold rle
        dsimp only
        rw [h.spike e hce hed hy]
        omega
      · have hxpos : 0 < x := by
          by_cases hx0 : x = 0
          · exfalso
            have hell0 := h.plateau e hce hed hy
            rw [hx0] at hell0
            omega
          · omega
        have hx1 : 1 ≤ x := by omega
        have hplat_present : c + x ≤ d := by omega
        have hde : dl ell e = (e : Int) - (x : Int) := delta_plateau h hce hed hy
        have hpl : (d : Int) - (x : Int) > s := by omega
        have hmem : platRecAll c d x s ∈ pCompAll c d x γ s := by simp [pCompAll]
        refine rle_trans _ _ _ ?_ (rle_rmaxList _ _ hmem)
        unfold platRecAll
        rw [if_pos ⟨hx1, hplat_present⟩]
        unfold platRec
        rw [if_pos hpl]
        unfold rle
        dsimp only
        rw [h.plateau e hce hed hy]
        omega
  · apply rmaxList_lub
    · exact hvb
    · intro r hr
      simp only [pCompAll, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · unfold rampRecAll
        by_cases hx2 : 2 ≤ x
        · rw [if_pos hx2]
          by_cases hs : (c : Int) - 1 > s
          · rw [if_pos hs]
            apply rle_rmaxList
            rw [mem_pBrute hcd]
            let e := min d (c + x - 2)
            refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
            · omega
            · exact Nat.min_le_left _ _
            · rw [h.ramp e (by omega) (Nat.min_le_left _ _) (by omega)]
              omega
            · rw [delta_ramp h (by omega) (Nat.min_le_left _ _) (by omega)]
              exact hs
            · rw [h.ramp e (by omega) (Nat.min_le_left _ _) (by omega)]
          · rw [if_neg hs]; exact valid_rle_unmatched _ hvb
        · rw [if_neg hx2]; exact valid_rle_unmatched _ hvb
      · unfold spikeRecAll
        by_cases hp : 1 ≤ x ∧ c + x - 1 ≤ d
        · rw [if_pos hp]
          unfold spikeRec
          by_cases hs : (c : Int) - 1 - (γ : Int) > s
          · rw [if_pos hs]
            apply rle_rmaxList
            rw [mem_pBrute hcd]
            let e := c + x - 1
            refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
            · omega
            · exact hp.2
            · rw [h.spike e (by omega) hp.2 (by omega)]
              omega
            · rw [delta_spike h (by omega) hp.2 (by omega)]
              exact hs
            · rw [h.spike e (by omega) hp.2 (by omega)]
          · rw [if_neg hs]; exact valid_rle_unmatched _ hvb
        · rw [if_neg hp]; exact valid_rle_unmatched _ hvb
      · unfold platRecAll
        by_cases hp : 1 ≤ x ∧ c + x ≤ d
        · rw [if_pos hp]
          unfold platRec
          by_cases hs : (d : Int) - (x : Int) > s
          · rw [if_pos hs]
            apply rle_rmaxList
            rw [mem_pBrute hcd]
            refine ⟨d, (by omega), Nat.le_refl d, ?_, ?_, ?_⟩
            · rw [h.plateau d (by omega) (Nat.le_refl d) (by omega)]
              omega
            · rw [delta_plateau h (by omega) (Nat.le_refl d) (by omega)]
              exact hs
            · rw [h.plateau d (by omega) (Nat.le_refl d) (by omega)]
          · rw [if_neg hs]; exact valid_rle_unmatched _ hvb
        · rw [if_neg hp]; exact valid_rle_unmatched _ hvb

/-- All-case E2: the plateau criterion is pointwise unconditional, while the
latest endpoint is a witness only when the plateau is non-empty. -/
theorem U_plateau_max_all {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    (s : Nat) :
    (∀ e, c ≤ e → e ≤ d → x < e - c + 1 →
        dl ell e ≤ (s : Int) → e ≤ min d (s + x))
    ∧ (c + x ≤ d → c ≤ s → dl ell (min d (s + x)) ≤ (s : Int)) := by
  constructor
  · intro e hce hed hy hdl
    rw [plateau_dl_le_iff h hce hed hy] at hdl
    omega
  · intro hp hcs
    let e := min d (s + x)
    have hce : c ≤ e := by omega
    have hed : e ≤ d := Nat.min_le_left _ _
    have hy : x < e - c + 1 := by omega
    rw [plateau_dl_le_iff h hce hed hy]
    omega

/-- E2 in the original non-empty-plateau shape; `hx` and `hcd` are no longer
needed as hypotheses. -/
theorem U_plateau_max_nonempty {ell : Nat → Nat} {c d x γ : Nat}
    (h : RspRow ell c d x γ) (hxd : c + x ≤ d) {s : Nat} (hcs : c ≤ s) :
    (∀ e, c ≤ e → e ≤ d → x < e - c + 1 → dl ell e ≤ (s : Int) → e ≤ min d (s + x))
    ∧ (dl ell (min d (s + x)) ≤ (s : Int)) := by
  exact ⟨(U_plateau_max_all h s).1, (U_plateau_max_all h s).2 hxd hcs⟩

/-- Exact all-case E3.  The old `c+x ≤ d` hypothesis was not used by the
mathematics; `2 ≤ x` is weakened to the semantic lower bound `1 ≤ x`. -/
theorem A_run_eq_all {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    (hx : 1 ≤ x) {E' : Nat} (hcE : c ≤ E') (hEd : E' ≤ d) :
    rmaxList (aBrute ell c E') = aComp ell c x γ E' := by
  have hellpos : 0 < ell E' := by
    rcases Nat.lt_trichotomy (E' - c + 1) x with h1 | h1 | h1
    · rw [h.ramp E' hcE hEd h1]; omega
    · rw [h.spike E' hcE hEd h1]; omega
    · rw [h.plateau E' hcE hEd h1]; omega
  have hmkE : CutArith.mk (ell E') (E' : Int) =
      (⟨(ell E' : Int), (E' : Int)⟩ : Route) :=
    CutArith.mk_pos _ _ (by omega)
  have hvB : Valid (rmaxList (aBrute ell c E')) := valid_rmaxList _ (valid_aBrute ell c E')
  have hvC : Valid (aComp ell c x γ E') := valid_aComp ell c x γ E' hx
  apply rle_antisymm
  · apply rmaxList_lub
    · exact hvC
    · intro r hr
      rw [mem_aBrute hcE] at hr
      obtain ⟨e, hce, hed, hpos, rfl⟩ := hr
      unfold aComp
      rw [hmkE]
      by_cases hs : c + x - 1 ≤ E'
      · rw [if_pos hs]
        rcases Nat.lt_trichotomy (e - c + 1) x with hy | hy | hy
        · have h1 : rle (⟨(ell e : Int), (e : Int)⟩ : Route)
              (⟨((x + γ : Nat) : Int), ((c + x - 1 : Nat) : Int)⟩ : Route) := by
            unfold rle; dsimp only; rw [h.ramp e hce (by omega) hy]; omega
          exact rle_trans _ _ _ h1 (rle_rmax_right _ _)
        · have h1 : rle (⟨(ell e : Int), (e : Int)⟩ : Route)
              (⟨((x + γ : Nat) : Int), ((c + x - 1 : Nat) : Int)⟩ : Route) := by
            unfold rle; dsimp only; rw [h.spike e hce (by omega) hy]; omega
          exact rle_trans _ _ _ h1 (rle_rmax_right _ _)
        · have h1 : rle (⟨(ell e : Int), (e : Int)⟩ : Route)
              (⟨(ell E' : Int), (E' : Int)⟩ : Route) := by
            unfold rle; dsimp only
            rw [h.plateau e hce (by omega) hy, h.plateau E' hcE hEd (by omega)]
            omega
          exact rle_trans _ _ _ h1 (rle_rmax_left _ _)
      · rw [if_neg hs]
        have h1 : rle (⟨(ell e : Int), (e : Int)⟩ : Route)
            (⟨(ell E' : Int), (E' : Int)⟩ : Route) := by
          unfold rle; dsimp only
          rw [h.ramp e hce (by omega) (by omega),
              h.ramp E' hcE hEd (by omega)]
          omega
        exact rle_trans _ _ _ h1 (rle_rmax_left _ _)
  · unfold aComp
    rw [hmkE]
    refine (rle_rmax_lub _ _ _).mpr ⟨?_, ?_⟩
    · apply rle_rmaxList
      rw [mem_aBrute hcE]
      exact ⟨E', hcE, Nat.le_refl E', hellpos, rfl⟩
    · by_cases hs : c + x - 1 ≤ E'
      · rw [if_pos hs]
        apply rle_rmaxList
        rw [mem_aBrute hcE]
        refine ⟨c + x - 1, by omega, by omega, ?_, ?_⟩
        · rw [h.spike _ (by omega) (by omega) (by omega)]; omega
        · rw [h.spike _ (by omega) (by omega) (by omega)]
      · rw [if_neg hs]; exact valid_rle_unmatched _ hvB

end RunHook

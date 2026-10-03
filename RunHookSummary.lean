import Std
import Route
import Lcs
import RunRectangle
import CutArith

/-!
## Phase E — run-compressed K-Hook summaries (§8)

A fixed output row `ell` restricted to a `α=β` K run `[c,d]` has the RSP shape:
ramp (`y<x`, `ℓ=y`), one spike (`y=x`, `ℓ=x+γ`), plateau (`y>x`, `ℓ=x`).
From this we read off the `δ = e-ℓ` shape and the per-run `P/U/A` summaries.
-/

open Route Lcs RunRect

namespace RunHook

set_option linter.unusedSectionVars false

/-- `δ_e = e - ℓ_e` (an `Int`; may be `-1`). -/
def dl (ell : Nat → Nat) (e : Nat) : Int := (e : Int) - (ell e : Int)

/-- RSP row shape of `ell` on `[c,d]` with Q-offset `x` and spike increment `γ`. -/
structure RspRow (ell : Nat → Nat) (c d x : Nat) (γ : Nat) : Prop where
  ramp : ∀ e, c ≤ e → e ≤ d → e - c + 1 < x → ell e = e - c + 1
  spike : ∀ e, c ≤ e → e ≤ d → e - c + 1 = x → ell e = x + γ
  plateau : ∀ e, c ≤ e → e ≤ d → x < e - c + 1 → ell e = x

/-- A real ROSA row (fixed `t`) realises the RSP shape on each equal-symbol K run. -/
theorem rspRow_of_rectangle {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    [DecidableEq α]
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c) {t : Nat} (ht : a ≤ t) (htb : t ≤ b) :
    RspRow (fun e => lcsLen q k t e) c d (t - a + 1) (lcsLen q k (a - 1) (c - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he hed hy
    rw [run_rectangle_rsp hQ hK heq ha hc ht htb he hed, if_pos hy]
  · intro e he hed hy
    rw [run_rectangle_rsp hQ hK heq ha hc ht htb he hed,
        if_neg (by omega : ¬ (e - c + 1 < t - a + 1)), if_pos hy]
  · intro e he hed hy
    rw [run_rectangle_rsp hQ hK heq ha hc ht htb he hed,
        if_neg (by omega : ¬ (e - c + 1 < t - a + 1)),
        if_neg (by omega : ¬ (e - c + 1 = t - a + 1))]

/-! ### δ shape (§8.1) -/

theorem delta_ramp {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    {e : Nat} (he : c ≤ e) (hed : e ≤ d) (hy : e - c + 1 < x) :
    dl ell e = (c : Int) - 1 := by
  unfold dl; rw [h.ramp e he hed hy]
  have hcast : ((e - c + 1 : Nat) : Int) = (e : Int) - (c : Int) + 1 := by omega
  rw [hcast]; omega

theorem delta_spike {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    {e : Nat} (he : c ≤ e) (hed : e ≤ d) (hy : e - c + 1 = x) :
    dl ell e = (c : Int) - 1 - (γ : Int) := by
  unfold dl; rw [h.spike e he hed hy]
  have hcast : ((x + γ : Nat) : Int) = (x : Int) + (γ : Int) := by omega
  rw [hcast]
  have : (x : Int) = (e : Int) - (c : Int) + 1 := by omega
  omega

theorem delta_plateau {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    {e : Nat} (he : c ≤ e) (hed : e ≤ d) (hy : x < e - c + 1) :
    dl ell e = (e : Int) - (x : Int) := by
  unfold dl; rw [h.plateau e he hed hy]

/-- On the plateau, `e = δ + x` (§8.3). -/
theorem plateau_e_eq_delta {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    {e : Nat} (he : c ≤ e) (hed : e ≤ d) (hy : x < e - c + 1) :
    (e : Int) = dl ell e + (x : Int) := by
  rw [delta_plateau h he hed hy]; omega


/-! ### E1 — compressed `P(s)` summary (§8.2) -/

def pBrute (ell : Nat → Nat) (c d : Nat) (s : Int) : List Route :=
  (((List.range (d - c + 1)).map (fun i => c + i)).filter
    (fun e => decide (0 < ell e ∧ s < dl ell e))).map
    (fun e => (⟨(ell e : Int), (e : Int)⟩ : Route))

def rampRec (c x : Nat) (s : Int) : Route :=
  if (c : Int) - 1 > s then (⟨((x - 1 : Nat) : Int), ((c + x - 2 : Nat) : Int)⟩ : Route) else unmatched

def spikeRec (c x γ : Nat) (s : Int) : Route :=
  if (c : Int) - 1 - (γ : Int) > s then
    (⟨((x + γ : Nat) : Int), ((c + x - 1 : Nat) : Int)⟩ : Route) else unmatched

def platRec (d x : Nat) (s : Int) : Route :=
  if (d : Int) - (x : Int) > s then (⟨((x : Nat) : Int), ((d : Nat) : Int)⟩ : Route) else unmatched

def pComp (c d x γ : Nat) (s : Int) : List Route :=
  [rampRec c x s, spikeRec c x γ s, platRec d x s]

theorem mem_pBrute {ell : Nat → Nat} {c d : Nat} {s : Int} {r : Route} (hcd : c ≤ d) :
    r ∈ pBrute ell c d s ↔
      ∃ e, c ≤ e ∧ e ≤ d ∧ 0 < ell e ∧ s < dl ell e ∧ (⟨(ell e : Int), (e : Int)⟩ : Route) = r := by
  unfold pBrute
  rw [List.mem_map]
  constructor
  · rintro ⟨e, he, hr⟩
    rw [List.mem_filter] at he
    obtain ⟨hm, hp⟩ := he
    rw [List.mem_map] at hm
    obtain ⟨i, hi, hie⟩ := hm
    rw [List.mem_range] at hi
    simp only [decide_eq_true_eq] at hp
    exact ⟨e, by omega, by omega, hp.1, hp.2, hr⟩
  · rintro ⟨e, hce, hed, hpos, hlt, hr⟩
    refine ⟨e, ?_, hr⟩
    rw [List.mem_filter]
    refine ⟨?_, by simp [hpos, hlt]⟩
    rw [List.mem_map]
    exact ⟨e - c, by rw [List.mem_range]; omega, by omega⟩

theorem valid_rampRec (c x : Nat) (s : Int) (hx : 2 ≤ x) : Valid (rampRec c x s) := by
  unfold rampRec
  by_cases h : (c : Int) - 1 > s
  · rw [if_pos h]
    refine ⟨?_, ?_, ?_⟩ <;> (dsimp only; try omega; try (intro h0; omega))
  · rw [if_neg h]; exact valid_unmatched

theorem valid_spikeRec (c x γ : Nat) (s : Int) (hx : 2 ≤ x) : Valid (spikeRec c x γ s) := by
  unfold spikeRec
  by_cases h : (c : Int) - 1 - (γ : Int) > s
  · rw [if_pos h]
    refine ⟨?_, ?_, ?_⟩ <;> (dsimp only; try omega; try (intro h0; omega))
  · rw [if_neg h]; exact valid_unmatched

theorem valid_platRec (d x : Nat) (s : Int) (hx : 2 ≤ x) : Valid (platRec d x s) := by
  unfold platRec
  by_cases h : (d : Int) - (x : Int) > s
  · rw [if_pos h]
    refine ⟨?_, ?_, ?_⟩ <;> (dsimp only; try omega; try (intro h0; omega))
  · rw [if_neg h]; exact valid_unmatched

theorem valid_pBrute (ell : Nat → Nat) (c d : Nat) (s : Int) :
    ∀ r ∈ pBrute ell c d s, Valid r := by
  intro r hr
  unfold pBrute at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, rfl⟩ := hr
  rw [List.mem_filter] at he
  obtain ⟨_, hp⟩ := he
  simp only [decide_eq_true_eq] at hp
  refine ⟨?_, ?_, ?_⟩ <;> (dsimp only; try omega; try (intro h0; omega))

theorem valid_pComp (c d x γ : Nat) (s : Int) (hx : 2 ≤ x) : ∀ r ∈ pComp c d x γ s, Valid r := by
  intro r hr
  simp only [pComp, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact valid_rampRec c x s hx
  · exact valid_spikeRec c x γ s hx
  · exact valid_platRec d x s hx

/-- `E1`: the per-run `P(s)` summary needs only the ramp-last, spike and
plateau-last records. -/
theorem P_run_eq {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    (hcd : c ≤ d) (hx : 2 ≤ x) (hxd : c + x ≤ d) (s : Int) :
    rmaxList (pBrute ell c d s) = rmaxList (pComp c d x γ s) := by
  have hvc : Valid (rmaxList (pComp c d x γ s)) := valid_rmaxList _ (valid_pComp c d x γ s hx)
  have hvb : Valid (rmaxList (pBrute ell c d s)) := valid_rmaxList _ (valid_pBrute ell c d s)
  apply rle_antisymm
  · apply rmaxList_lub
    · exact hvc
    · intro r hr
      rw [mem_pBrute hcd] at hr
      obtain ⟨e, hce, hed, hpos, hlt, rfl⟩ := hr
      rcases Nat.lt_trichotomy (e - c + 1) x with hy | hy | hy
      · have hde : dl ell e = (c : Int) - 1 := delta_ramp h hce hed hy
        have hramp : (c : Int) - 1 > s := by rw [← hde]; exact hlt
        have h1 : rle (⟨(ell e : Int), (e : Int)⟩ : Route) (rampRec c x s) := by
          unfold rampRec; rw [if_pos hramp]; unfold rle; dsimp only
          rw [h.ramp e hce hed hy]; omega
        exact rle_trans _ _ _ h1 (rle_rmaxList _ _ (by simp [pComp]))
      · have hde : dl ell e = (c : Int) - 1 - (γ : Int) := delta_spike h hce hed hy
        have hsp : (c : Int) - 1 - (γ : Int) > s := by rw [← hde]; exact hlt
        have h1 : rle (⟨(ell e : Int), (e : Int)⟩ : Route) (spikeRec c x γ s) := by
          unfold spikeRec; rw [if_pos hsp]; unfold rle; dsimp only
          rw [h.spike e hce hed hy]; omega
        exact rle_trans _ _ _ h1 (rle_rmaxList _ _ (by simp [pComp]))
      · have hde : dl ell e = (e : Int) - (x : Int) := delta_plateau h hce hed hy
        have hpl : (d : Int) - (x : Int) > s := by omega
        have h1 : rle (⟨(ell e : Int), (e : Int)⟩ : Route) (platRec d x s) := by
          unfold platRec; rw [if_pos hpl]; unfold rle; dsimp only
          rw [h.plateau e hce hed hy]; omega
        exact rle_trans _ _ _ h1 (rle_rmaxList _ _ (by simp [pComp]))
  · apply rmaxList_lub
    · exact hvb
    · intro r hr
      simp only [pComp, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · unfold rampRec
        by_cases hc1 : (c : Int) - 1 > s
        · rw [if_pos hc1]
          apply rle_rmaxList
          rw [mem_pBrute hcd]
          refine ⟨c + x - 2, by omega, by omega, ?_, ?_, ?_⟩
          · rw [h.ramp _ (by omega) (by omega) (by omega)]; omega
          · rw [delta_ramp h (by omega) (by omega) (by omega)]; omega
          · have hidx : (c + x - 2) - c + 1 = x - 1 := by omega
            rw [h.ramp _ (by omega) (by omega) (by omega), hidx]
        · rw [if_neg hc1]; exact valid_rle_unmatched _ hvb
      · unfold spikeRec
        by_cases hc1 : (c : Int) - 1 - (γ : Int) > s
        · rw [if_pos hc1]
          apply rle_rmaxList
          rw [mem_pBrute hcd]
          refine ⟨c + x - 1, by omega, by omega, ?_, ?_, ?_⟩
          · rw [h.spike _ (by omega) (by omega) (by omega)]; omega
          · rw [delta_spike h (by omega) (by omega) (by omega)]; omega
          · rw [h.spike _ (by omega) (by omega) (by omega)]
        · rw [if_neg hc1]; exact valid_rle_unmatched _ hvb
      · unfold platRec
        by_cases hc1 : (d : Int) - (x : Int) > s
        · rw [if_pos hc1]
          apply rle_rmaxList
          rw [mem_pBrute hcd]
          refine ⟨d, by omega, by omega, ?_, ?_, ?_⟩
          · rw [h.plateau _ (by omega) (by omega) (by omega)]; omega
          · rw [delta_plateau h (by omega) (by omega) (by omega)]; omega
          · rw [h.plateau _ (by omega) (by omega) (by omega)]
        · rw [if_neg hc1]; exact valid_rle_unmatched _ hvb

/-! ### E2 — compressed `U(s)` summary (§8.3) -/

/-- On the plateau, `δ_e ≤ s ↔ e ≤ s + x`. -/
theorem plateau_dl_le_iff {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    {e : Nat} (he : c ≤ e) (hed : e ≤ d) (hy : x < e - c + 1) (s : Int) :
    (dl ell e ≤ s ↔ (e : Int) ≤ s + (x : Int)) := by
  rw [delta_plateau h he hed hy]; omega

/-- `U(s)` plateau summary: the plateau endpoints reaching `δ ≤ s` are exactly
those with `e ≤ s+x`; the latest one is `min d (s+x)`. -/
theorem U_plateau_max {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    (hcd : c ≤ d) (hx : 2 ≤ x) (hxd : c + x ≤ d) {s : Nat} (hcs : c ≤ s) :
    (∀ e, c ≤ e → e ≤ d → x < e - c + 1 → dl ell e ≤ (s : Int) → e ≤ min d (s + x))
    ∧ (dl ell (min d (s + x)) ≤ (s : Int)) := by
  constructor
  · intro e hce hed hy hdl
    rw [plateau_dl_le_iff h hce hed hy] at hdl
    omega
  · have hge : c + x ≤ min d (s + x) := by omega
    have hle : min d (s + x) ≤ d := Nat.min_le_left _ _
    have hy : x < min d (s + x) - c + 1 := by omega
    rw [plateau_dl_le_iff h (by omega) hle hy]
    omega

/-! ### E3 — compressed `A(s)` summary (§8.4) -/

/-- Brute prefix max over run `[c,E']`. -/
def aBrute (ell : Nat → Nat) (c E' : Nat) : List Route :=
  (((List.range (E' - c + 1)).map (fun i => c + i)).filter (fun e => decide (0 < ell e))).map
    (fun e => (⟨(ell e : Int), (e : Int)⟩ : Route))

/-- Compressed prefix winner: the last endpoint plus the (at most one) spike. -/
def aComp (ell : Nat → Nat) (c x γ : Nat) (E' : Nat) : Route :=
  rmax (CutArith.mk (ell E') (E' : Int))
       (if c + x - 1 ≤ E' then
          (⟨((x + γ : Nat) : Int), ((c + x - 1 : Nat) : Int)⟩ : Route) else unmatched)

theorem mem_aBrute {ell : Nat → Nat} {c E' : Nat} {r : Route} (hcE : c ≤ E') :
    r ∈ aBrute ell c E' ↔
      ∃ e, c ≤ e ∧ e ≤ E' ∧ 0 < ell e ∧ (⟨(ell e : Int), (e : Int)⟩ : Route) = r := by
  unfold aBrute
  rw [List.mem_map]
  constructor
  · rintro ⟨e, he, hr⟩
    rw [List.mem_filter] at he
    obtain ⟨hm, hp⟩ := he
    rw [List.mem_map] at hm
    obtain ⟨i, hi, hie⟩ := hm
    rw [List.mem_range] at hi
    simp only [decide_eq_true_eq] at hp
    exact ⟨e, by omega, by omega, hp, hr⟩
  · rintro ⟨e, hce, hed, hpos, hr⟩
    refine ⟨e, ?_, hr⟩
    rw [List.mem_filter]
    refine ⟨?_, by simp [hpos]⟩
    rw [List.mem_map]
    exact ⟨e - c, by rw [List.mem_range]; omega, by omega⟩

theorem valid_aBrute (ell : Nat → Nat) (c E' : Nat) : ∀ r ∈ aBrute ell c E', Valid r := by
  intro r hr
  unfold aBrute at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, rfl⟩ := hr
  rw [List.mem_filter] at he
  obtain ⟨_, hp⟩ := he
  simp only [decide_eq_true_eq] at hp
  refine ⟨?_, ?_, ?_⟩ <;> (dsimp only; try omega; try (intro h0; omega))

theorem valid_aComp (ell : Nat → Nat) (c x γ : Nat) (E' : Nat) (hx : 1 ≤ x) :
    Valid (aComp ell c x γ E') := by
  unfold aComp
  apply valid_rmax
  · exact CutArith.valid_mk _ _ (by omega)
  · by_cases h : c + x - 1 ≤ E'
    · rw [if_pos h]
      refine ⟨?_, ?_, ?_⟩ <;> (dsimp only; try omega; try (intro h0; omega))
    · rw [if_neg h]; exact valid_unmatched

theorem A_run_eq {ell : Nat → Nat} {c d x γ : Nat} (h : RspRow ell c d x γ)
    (hcd : c ≤ d) (hx : 2 ≤ x) (hxd : c + x ≤ d) {E' : Nat} (hcE : c ≤ E') (hEd : E' ≤ d) :
    rmaxList (aBrute ell c E') = aComp ell c x γ E' := by
  have hellpos : 0 < ell E' := by
    rcases Nat.lt_trichotomy (E' - c + 1) x with h1 | h1 | h1
    · rw [h.ramp E' hcE hEd h1]; omega
    · rw [h.spike E' hcE hEd h1]; omega
    · rw [h.plateau E' hcE hEd h1]; omega
  have hmkE : CutArith.mk (ell E') (E' : Int) = (⟨(ell E' : Int), (E' : Int)⟩ : Route) :=
    CutArith.mk_pos _ _ (by omega)
  have hvB : Valid (rmaxList (aBrute ell c E')) := valid_rmaxList _ (valid_aBrute ell c E')
  have hvC : Valid (aComp ell c x γ E') := valid_aComp ell c x γ E' (by omega)
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
          rw [h.ramp e hce (by omega) (by omega), h.ramp E' hcE hEd (by omega)]
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

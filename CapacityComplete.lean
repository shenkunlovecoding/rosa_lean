import Capacity
import RunHookSummary

/-!
## Phase D completion — explicit run-capacity argmax

`Capacity.run_capacity_latest_endpoint` proves the three-way threshold
classification, but does not name the largest endpoint in `[c,d]` that reaches
`lam`.  This file closes that semantic gap for one fixed run rectangle.

For a same-symbol rectangle with

* `x = t-a+1` (Q offset),
* `n = d-c+1` (K-run length),
* `p = c+x-1` (the diagonal spike endpoint),
* `gamma = lcsLen q k (a-1) (c-1)`,

the capacity records are

* ordinary: length `min x n`, endpoint `d`;
* spike:     length `x+gamma`, endpoint `p` (when `p <= d`).

The first theorem below returns the exact maximum reaching endpoint; the
record theorems prove that the ordinary/spike pair is an exact max-envelope and
that ties prefer the ordinary record (the later endpoint).
-/

open Lcs Route RunRect

namespace Capacity

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α]

/-- The predicate `e ∈ [c,d]` reaches threshold `lam` in a fixed RSP row. -/
def ReachesAt (q k : Nat → α) (t c d lam : Nat) (e : Nat) : Prop :=
  c ≤ e ∧ e ≤ d ∧ lam ≤ lcsLen q k t e

/-- `e` is the largest endpoint in `[c,d]` reaching `lam`. -/
def IsMaxReaching (q k : Nat → α) (t c d lam : Nat) (e : Nat) : Prop :=
  ReachesAt q k t c d lam e ∧
    ∀ e', ReachesAt q k t c d lam e' → e' ≤ e

/-- The ordinary Q-run capacity record: `(min x n, d)`. -/
def ordinaryCap (x n : Nat) : Nat := min x n

/-- The diagonal spike capacity record: `(x + gamma, c+x-1)`. -/
def spikeCap (x gamma : Nat) : Nat := x + gamma

/-- The diagonal spike endpoint `c+x-1`. -/
def spikeEndpoint (c x : Nat) : Nat := c + x - 1

/-- Ordinary record `(min x n, d)` from the Q baseline envelope. -/
def ordinaryRecord (c d x : Nat) : Route :=
  ⟨((ordinaryCap x (d - c + 1) : Nat) : Int), (d : Int)⟩

/-- Spike record `(x+gamma, c+x-1)`, or `unmatched` when the spike is outside
the truncated K run. -/
def spikeRecord (c d x gamma : Nat) : Route :=
  if spikeEndpoint c x ≤ d then
    ⟨((spikeCap x gamma : Nat) : Int), ((spikeEndpoint c x : Nat) : Int)⟩
  else
    unmatched

/-- The exact maximum endpoint reaching `lam`: ordinary plateau/last endpoint,
then the diagonal spike, then none. -/
def maxEndpoint? (q k : Nat → α) (a _b c d t lam : Nat) : Option Nat :=
  if lam ≤ ordinaryCap (t - a + 1) (d - c + 1) then
    some d
  else if spikeEndpoint c (t - a + 1) ≤ d ∧
      lam ≤ spikeCap (t - a + 1) (lcsLen q k (a - 1) (c - 1)) then
    some (spikeEndpoint c (t - a + 1))
  else
    none

/-- Explicit max-endpoint closure for one `α=β` run rectangle. -/
theorem run_capacity_maxEndpoint?_correct {q k : Nat → α} {Tq Tk a b c d : Nat}
    {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c) (hcd : c ≤ d)
    {t : Nat} (ht : a ≤ t) (htb : t ≤ b) {lam : Nat} :
    match maxEndpoint? q k a b c d t lam with
    | some e => IsMaxReaching q k t c d lam e
    | none => ∀ e, c ≤ e → e ≤ d → ¬ (lam ≤ lcsLen q k t e) := by
  have hxpos : 0 < t - a + 1 := by omega
  have hmain := run_capacity_latest_endpoint hQ hK heq ha hc hcd ht htb (lam := lam)
  unfold maxEndpoint? ordinaryCap spikeCap spikeEndpoint
  by_cases hord : lam ≤ min (t - a + 1) (d - c + 1)
  · rw [if_pos hord]
    refine ⟨⟨hcd, Nat.le_refl d, hmain.1 hord⟩, ?_⟩
    intro e he
    exact he.2.1
  · rw [if_neg hord]
    by_cases hsp : c + (t - a + 1) - 1 ≤ d ∧
        lam ≤ (t - a + 1) + lcsLen q k (a - 1) (c - 1)
    · rw [if_pos hsp]
      have hgt : min (t - a + 1) (d - c + 1) < lam := Nat.lt_of_not_ge hord
      have hxn : t - a + 1 ≤ d - c + 1 := by omega
      have hreach := hmain.2.1 hgt hxn hsp.2
      refine ⟨⟨by omega, hsp.1, hreach⟩, ?_⟩
      intro e he
      have hmem := (run_capacity_reaches hQ hK heq ha hc ht htb he.1 he.2.1
        (lam := lam)).mp he.2.2
      rcases hmem with hramp | hspike | hplateau
      · have hxlt : t - a + 1 < lam := by omega
        omega
      · omega
      · have hxlt : t - a + 1 < lam := by omega
        omega
    · rw [if_neg hsp]
      have hgt : min (t - a + 1) (d - c + 1) < lam := Nat.lt_of_not_ge hord
      have hdisj : d - c + 1 < t - a + 1 ∨
          (t - a + 1) + lcsLen q k (a - 1) (c - 1) < lam := by
        by_cases hpn : c + (t - a + 1) - 1 ≤ d
        · right
          have hs : ¬ lam ≤ (t - a + 1) + lcsLen q k (a - 1) (c - 1) := by
            intro hs
            exact hsp ⟨hpn, hs⟩
          omega
        · left
          omega
      exact hmain.2.2 hgt hdisj

/-- A `some` result of `maxEndpoint?` is exactly the maximum reaching endpoint. -/
theorem run_capacity_some_endpoint_is_max {q k : Nat → α}
    {Tq Tk a b c d t lam e : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c) (hcd : c ≤ d)
    (ht : a ≤ t) (htb : t ≤ b)
    (hsome : maxEndpoint? q k a b c d t lam = some e) :
    IsMaxReaching q k t c d lam e := by
  have h := run_capacity_maxEndpoint?_correct hQ hK heq ha hc hcd ht htb (lam := lam)
  simpa [hsome] using h

/-- A `none` result of `maxEndpoint?` means that every endpoint in the
truncated K run fails the threshold. -/
theorem run_capacity_none_endpoint_fails {q k : Nat → α}
    {Tq Tk a b c d t lam : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c) (hcd : c ≤ d)
    (ht : a ≤ t) (htb : t ≤ b)
    (hnone : maxEndpoint? q k a b c d t lam = none) :
    ∀ e, c ≤ e → e ≤ d → ¬ (lam ≤ lcsLen q k t e) := by
  have h := run_capacity_maxEndpoint?_correct hQ hK heq ha hc hcd ht htb (lam := lam)
  simpa [hnone] using h

/-- The threshold has an endpoint in `[c,d]` exactly when `maxEndpoint?` is
not `none`. -/
theorem run_capacity_argmax_exists_iff {q k : Nat → α}
    {Tq Tk a b c d t lam : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c) (hcd : c ≤ d)
    (ht : a ≤ t) (htb : t ≤ b) :
    (∃ e, ReachesAt q k t c d lam e) ↔
      maxEndpoint? q k a b c d t lam ≠ none := by
  constructor
  · rintro ⟨e, he⟩ hnone
    exact run_capacity_none_endpoint_fails hQ hK heq ha hc hcd ht htb hnone
      e he.1 he.2.1 he.2.2
  · intro hne
    cases h : maxEndpoint? q k a b c d t lam with
    | none => exact (hne h).elim
    | some e =>
        have hm := run_capacity_some_endpoint_is_max hQ hK heq ha hc hcd ht htb h
        exact ⟨e, hm.1⟩

/-- Exact branch characterisation of the returned maximum endpoint. -/
theorem run_capacity_maxEndpoint?_eq_some_iff {q k : Nat → α}
    {a b c d t lam e : Nat} :
    maxEndpoint? q k a b c d t lam = some e ↔
      (e = d ∧ lam ≤ ordinaryCap (t - a + 1) (d - c + 1)) ∨
      (e = spikeEndpoint c (t - a + 1) ∧
        ordinaryCap (t - a + 1) (d - c + 1) < lam ∧
        spikeEndpoint c (t - a + 1) ≤ d ∧
        lam ≤ spikeCap (t - a + 1) (lcsLen q k (a - 1) (c - 1))) := by
  unfold maxEndpoint?
  by_cases hord : lam ≤ ordinaryCap (t - a + 1) (d - c + 1)
  · rw [if_pos hord]
    constructor
    · intro h
      left
      exact ⟨(Option.some.inj h).symm, hord⟩
    · rintro (⟨rfl, _⟩ | ⟨rfl, hgt, _⟩)
      · rfl
      · omega
  · rw [if_neg hord]
    by_cases hsp : spikeEndpoint c (t - a + 1) ≤ d ∧
        lam ≤ spikeCap (t - a + 1) (lcsLen q k (a - 1) (c - 1))
    · rw [if_pos hsp]
      constructor
      · intro h
        right
        refine ⟨(Option.some.inj h).symm, Nat.lt_of_not_ge hord, hsp.1, hsp.2⟩
      · rintro (⟨rfl, hle⟩ | ⟨rfl, _, _, _⟩)
        · exact (hord hle).elim
        · rfl
    · rw [if_neg hsp]
      constructor
      · intro h; cases h
      · rintro (⟨rfl, hle⟩ | ⟨rfl, _, hp, hspike⟩)
        · exact (hord hle).elim
        · exact (hsp ⟨hp, hspike⟩).elim

/-! ### Two-record exact envelope -/

/-- All endpoint routes of one RSP row, with non-positive lengths normalized. -/
def rspEndpointRoutes (ell : Nat → Nat) (c d : Nat) : List Route :=
  ((List.range (d - c + 1)).map (fun i => c + i)).map
    (fun e => CutArith.mk ((ell e : Nat) : Int) (e : Int))

private theorem valid_ordinaryRecord {c d x : Nat} (hx : 0 < x) :
    Valid (ordinaryRecord c d x) := by
  unfold ordinaryRecord ordinaryCap
  apply CutArith.valid_pair
  · change (0 : Int) < ((min x (d - c + 1) : Nat) : Int)
    omega
  · omega

private theorem valid_spikeRecord {c d x gamma : Nat} (hx : 0 < x) :
    Valid (spikeRecord c d x gamma) := by
  unfold spikeRecord spikeEndpoint spikeCap
  by_cases hp : c + x - 1 ≤ d
  · rw [if_pos hp]
    apply CutArith.valid_pair
    · change (0 : Int) < ((x + gamma : Nat) : Int)
      omega
    · change (-1 : Int) ≤ ((c + x - 1 : Nat) : Int)
      omega
  · rw [if_neg hp]
    exact valid_unmatched

private theorem rle_pair_nat {l l' e e' : Nat} (hl : l ≤ l')
    (heq : l = l' → e ≤ e') :
    rle (⟨(l : Int), (e : Int)⟩ : Route) (⟨(l' : Int), (e' : Int)⟩ : Route) := by
  unfold rle
  dsimp only
  by_cases h : l = l'
  · right
    exact ⟨by omega, by exact_mod_cast heq h⟩
  · left
    omega

private theorem rle_mk_nat {l l' e e' : Nat} (hl : l ≤ l')
    (heq : l = l' → e ≤ e') :
    rle (CutArith.mk (l : Int) (e : Int))
        (CutArith.mk (l' : Int) (e' : Int)) := by
  by_cases hl0 : l = 0
  · subst l
    rw [CutArith.mk_nonpos _ _ (by omega)]
    exact valid_rle_unmatched _ (CutArith.valid_mk _ _ (by omega))
  · have hpos : 0 < l := Nat.pos_of_ne_zero hl0
    have hpos' : 0 < l' := by omega
    rw [CutArith.mk_pos _ _ (by omega), CutArith.mk_pos _ _ (by omega)]
    exact rle_pair_nat hl heq

private theorem mem_rspEndpointRoutes {ell : Nat → Nat} {c d e : Nat}
    (hce : c ≤ e) (hed : e ≤ d) :
    CutArith.mk ((ell e : Nat) : Int) (e : Int) ∈ rspEndpointRoutes ell c d := by
  unfold rspEndpointRoutes
  rw [List.mem_map]
  refine ⟨e, ?_, rfl⟩
  rw [List.mem_map]
  refine ⟨e - c, ?_, ?_⟩
  · rw [List.mem_range]
    omega
  · omega

private theorem valid_rspEndpointRoutes (ell : Nat → Nat) (c d : Nat) :
    ∀ r ∈ rspEndpointRoutes ell c d, Valid r := by
  intro r hr
  unfold rspEndpointRoutes at hr
  rw [List.mem_map] at hr
  obtain ⟨e, _, rfl⟩ := hr
  exact CutArith.valid_mk _ _ (by omega)

private theorem rsp_route_le_records {ell : Nat → Nat} {c d x gamma : Nat}
    (h : RunHook.RspRow ell c d x gamma) (hx : 0 < x)
    {e : Nat} (hce : c ≤ e) (hed : e ≤ d) :
    rle (CutArith.mk ((ell e : Nat) : Int) (e : Int))
      (rmax (ordinaryRecord c d x) (spikeRecord c d x gamma)) := by
  by_cases hyx : e - c + 1 < x
  · rw [h.ramp e hce hed hyx]
    by_cases hp : spikeEndpoint c x ≤ d
    · apply rle_trans _ _ _ ?_ (rle_rmax_right _ _)
      change c + x - 1 ≤ d at hp
      rw [CutArith.mk_pos _ _ (by omega)]
      unfold spikeRecord spikeEndpoint spikeCap
      rw [if_pos hp]
      apply rle_pair_nat
      · omega
      · intro heq
        omega
    · apply rle_trans _ _ _ ?_ (rle_rmax_left _ _)
      rw [CutArith.mk_pos _ _ (by omega)]
      unfold ordinaryRecord ordinaryCap
      apply rle_pair_nat
      · omega
      · intro heq
        omega
  · by_cases hyeq : e - c + 1 = x
    · have hep : e = spikeEndpoint c x := by
        unfold spikeEndpoint
        omega
      subst e
      rw [h.spike _ (by omega) (by omega) (by omega)]
      have hp : spikeEndpoint c x ≤ d := by
        unfold spikeEndpoint
        omega
      apply rle_trans _ _ _ ?_ (rle_rmax_right _ _)
      change c + x - 1 ≤ d at hp
      rw [CutArith.mk_pos _ _ (by omega)]
      unfold spikeRecord spikeEndpoint spikeCap
      rw [if_pos hp]
      exact rle_refl _
    · have hxy : x < e - c + 1 := by omega
      rw [h.plateau e hce hed hxy]
      apply rle_trans _ _ _ ?_ (rle_rmax_left _ _)
      rw [CutArith.mk_pos _ _ (by omega)]
      unfold ordinaryRecord ordinaryCap
      apply rle_pair_nat
      · omega
      · intro heq
        omega

private theorem ordinaryRecord_le_diagonal {ell : Nat → Nat} {c d x gamma : Nat}
    (h : RunHook.RspRow ell c d x gamma) (hcd : c ≤ d) (hx : 0 < x) :
    rle (ordinaryRecord c d x)
      (CutArith.mk ((ell d : Nat) : Int) (d : Int)) := by
  have hdpos : 0 < ell d := by
    rcases Nat.lt_trichotomy (d - c + 1) x with hlt | heq | hgt
    · rw [h.ramp d hcd (Nat.le_refl d) hlt]
      omega
    · rw [h.spike d hcd (Nat.le_refl d) heq]
      omega
    · rw [h.plateau d hcd (Nat.le_refl d) hgt]
      omega
  rw [CutArith.mk_pos _ _ (by omega)]
  unfold ordinaryRecord ordinaryCap
  apply rle_pair_nat
  · rcases Nat.lt_trichotomy (d - c + 1) x with hlt | heq | hgt
    · rw [h.ramp d hcd (Nat.le_refl d) hlt]
      omega
    · rw [h.spike d hcd (Nat.le_refl d) heq]
      omega
    · rw [h.plateau d hcd (Nat.le_refl d) hgt]
      omega
  · intro _
    omega

private theorem spikeRecord_mem_rspEndpointRoutes {ell : Nat → Nat} {c d x gamma : Nat}
    (h : RunHook.RspRow ell c d x gamma) (hx : 0 < x)
    (hp : spikeEndpoint c x ≤ d) :
    spikeRecord c d x gamma ∈ rspEndpointRoutes ell c d := by
  have hp_ge : c ≤ spikeEndpoint c x := by
    unfold spikeEndpoint
    omega
  have hmem := mem_rspEndpointRoutes (ell := ell) hp_ge hp
  have hs : ell (spikeEndpoint c x) = x + gamma := by
    apply h.spike
    · exact hp_ge
    · exact hp
    · unfold spikeEndpoint
      omega
  have hp' : c + x - 1 ≤ d := by simpa [spikeEndpoint] using hp
  unfold spikeRecord spikeEndpoint spikeCap at *
  rw [if_pos hp']
  rw [CutArith.mk_pos _ _ (by omega)] at hmem
  simpa [hs] using hmem

private theorem records_le_rsp_maxList {ell : Nat → Nat} {c d x gamma : Nat}
    (h : RunHook.RspRow ell c d x gamma) (hcd : c ≤ d) (hx : 0 < x) :
    rle (rmax (ordinaryRecord c d x) (spikeRecord c d x gamma))
      (rmaxList (rspEndpointRoutes ell c d)) := by
  have hvOrd : Valid (ordinaryRecord c d x) := valid_ordinaryRecord hx
  have hvSpike : Valid (spikeRecord c d x gamma) := valid_spikeRecord hx
  have hvList : Valid (rmaxList (rspEndpointRoutes ell c d)) :=
    valid_rmaxList _ (valid_rspEndpointRoutes ell c d)
  apply (rle_rmax_lub _ _ _).mpr
  constructor
  · have hmem : CutArith.mk ((ell d : Nat) : Int) (d : Int) ∈ rspEndpointRoutes ell c d :=
      mem_rspEndpointRoutes (ell := ell) hcd (Nat.le_refl d)
    exact rle_trans _ _ _ (ordinaryRecord_le_diagonal h hcd hx)
      (rle_rmaxList _ _ hmem)
  · by_cases hp : spikeEndpoint c x ≤ d
    · exact rle_rmaxList _ _ (spikeRecord_mem_rspEndpointRoutes h hx hp)
    · unfold spikeRecord
      rw [if_neg hp]
      exact valid_rle_unmatched _ hvList

/-- The ordinary and diagonal-spike records are an exact max-envelope for one
fixed RSP row. -/
theorem rsp_two_records_sufficient {ell : Nat → Nat} {c d x gamma : Nat}
    (h : RunHook.RspRow ell c d x gamma) (hcd : c ≤ d) (hx : 0 < x) :
    rmaxList (rspEndpointRoutes ell c d) =
      rmax (ordinaryRecord c d x) (spikeRecord c d x gamma) := by
  apply rle_antisymm
  · apply rmaxList_lub
    · exact valid_rmax _ _ (valid_ordinaryRecord hx) (valid_spikeRecord hx)
    · intro r hr
      unfold rspEndpointRoutes at hr
      rw [List.mem_map] at hr
      obtain ⟨e, he, rfl⟩ := hr
      rw [List.mem_map] at he
      obtain ⟨i, hi, hie⟩ := he
      rw [List.mem_range] at hi
      exact rsp_route_le_records h hx (by omega) (by omega)
  · exact records_le_rsp_maxList h hcd hx

/-- Same-symbol run-rectangle instance of `rsp_two_records_sufficient`. -/
theorem run_capacity_two_records_sufficient {q k : Nat → α}
    {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c) (hcd : c ≤ d)
    {t : Nat} (ht : a ≤ t) (htb : t ≤ b) :
    rmaxList (rspEndpointRoutes (fun e => lcsLen q k t e) c d) =
      rmax (ordinaryRecord c d (t - a + 1))
        (spikeRecord c d (t - a + 1) (lcsLen q k (a - 1) (c - 1))) := by
  exact rsp_two_records_sufficient
    (RunHook.rspRow_of_rectangle hQ hK heq ha hc ht htb) hcd (by omega)

/-- If the spike capacity does not exceed the ordinary capacity, the ordinary
record wins; equality is the tie case and selects the later endpoint `d`. -/
theorem ordinaryRecord_wins_of_spikeCap_le {c d x gamma : Nat}
    (hfeas : spikeEndpoint c x ≤ d)
    (hle : spikeCap x gamma ≤ ordinaryCap x (d - c + 1)) :
    rmax (ordinaryRecord c d x) (spikeRecord c d x gamma) =
      ordinaryRecord c d x := by
  apply rle_antisymm
  · apply (rle_rmax_lub _ _ _).mpr
    constructor
    · exact rle_refl _
    · have hfeas' : c + x - 1 ≤ d := by simpa [spikeEndpoint] using hfeas
      unfold ordinaryRecord spikeRecord spikeCap ordinaryCap spikeEndpoint
      rw [if_pos hfeas']
      apply rle_pair_nat hle
      intro _
      omega
  · exact rle_rmax_left _ _

/-- If the spike capacity strictly exceeds the ordinary capacity and the spike
endpoint is feasible, the spike record wins. -/
theorem spikeRecord_wins_of_ordinaryCap_lt {c d x gamma : Nat}
    (hfeas : spikeEndpoint c x ≤ d)
    (hlt : ordinaryCap x (d - c + 1) < spikeCap x gamma) :
    rmax (ordinaryRecord c d x) (spikeRecord c d x gamma) =
      spikeRecord c d x gamma := by
  apply rle_antisymm
  · apply (rle_rmax_lub _ _ _).mpr
    constructor
    · have hfeas' : c + x - 1 ≤ d := by simpa [spikeEndpoint] using hfeas
      have hne : ordinaryCap x (d - c + 1) ≠ spikeCap x gamma := Nat.ne_of_lt hlt
      unfold ordinaryRecord spikeRecord spikeCap ordinaryCap spikeEndpoint
      rw [if_pos hfeas']
      apply rle_pair_nat (by omega)
      intro heq
      exact False.elim (hne (by exact_mod_cast heq))
    · exact rle_refl _
  · exact rle_rmax_right _ _

/-- Explicit tie rule: equal ordinary and spike capacities select the ordinary
record, whose endpoint is `d` (the larger endpoint unless both endpoints
coincide). -/
theorem ordinaryRecord_wins_tie {c d x gamma : Nat}
    (hfeas : spikeEndpoint c x ≤ d)
    (htie : ordinaryCap x (d - c + 1) = spikeCap x gamma) :
    rmax (ordinaryRecord c d x) (spikeRecord c d x gamma) =
      ordinaryRecord c d x :=
  ordinaryRecord_wins_of_spikeCap_le hfeas (by omega)

end Capacity

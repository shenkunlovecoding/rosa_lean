import CapacityComplete
import QCut

/-!
## Phase D — multi-run capacity-record aggregation

This file closes the aggregation layer left implicit in §7 of the ROSA notes.
A `CapacityRecord` is the pair `(capacity, endpoint)` supplied by one active K
run.  Two different maxima are kept separate:

* `globalRoute` uses `rmaxList`, hence its primary key is capacity and its
  tie-break is the largest endpoint among the maximum-capacity records;
* `latestAt rs lam` uses only the records with capacity at least `lam`, then
  takes the largest endpoint.  This is the endpoint semantics consumed by
  `QCut.qcutClosed`.

The final bridge is conditional on `CompleteAt`: every causal endpoint is
represented, every record points to a causal endpoint, and each record's
capacity is exactly the row value at that endpoint.  These hypotheses are part
of the theorem boundary; no claim is made about an incomplete record set.
-/

open Route
open Capacity

namespace CapacityMultiRun

/-- A capacity record `(capacity, endpoint)` contributed by one active K run. -/
structure CapacityRecord where
  cap : Nat
  endpoint : Nat
deriving DecidableEq, Repr

namespace CapacityRecord

/-- The ROSA route induced by a capacity record.  Non-positive lengths are
normalized to the unmatched route by `CutArith.mk`. -/
def toRoute (r : CapacityRecord) : Route :=
  CutArith.mk (r.cap : Int) (r.endpoint : Int)

theorem toRoute_eq_of_pos {r : CapacityRecord} (h : 0 < r.cap) :
    r.toRoute = ⟨(r.cap : Int), (r.endpoint : Int)⟩ := by
  unfold toRoute
  exact CutArith.mk_pos _ _ (by exact_mod_cast h)

theorem toRoute_eq_unmatched_of_zero {r : CapacityRecord} (h : r.cap = 0) :
    r.toRoute = unmatched := by
  unfold toRoute
  rw [h]
  exact CutArith.mk_nonpos 0 0 (by omega)

theorem valid_toRoute (r : CapacityRecord) : Valid r.toRoute := by
  unfold toRoute
  exact CutArith.valid_mk _ _ (by omega)

theorem toRoute_len_lt_of_cap_lt {r : CapacityRecord} {m : Nat}
    (h : r.cap < m) : r.toRoute.len < (m : Int) := by
  by_cases hzero : r.cap = 0
  · rw [toRoute_eq_unmatched_of_zero hzero]
    simp [unmatched]
    omega
  · rw [toRoute_eq_of_pos (Nat.pos_of_ne_zero hzero)]
    change (r.cap : Int) < (m : Int)
    exact_mod_cast h

end CapacityRecord

/-- Maximum capacity in a finite record set (`0` for the empty set). -/
def maxCap : List CapacityRecord → Nat
  | [] => 0
  | r :: rs => max r.cap (maxCap rs)

theorem cap_le_maxCap {r : CapacityRecord} {rs : List CapacityRecord}
    (hr : r ∈ rs) : r.cap ≤ maxCap rs := by
  induction rs with
  | nil => simp at hr
  | cons s ss ih =>
      simp only [maxCap]
      rcases List.mem_cons.mp hr with h | h
      · subst h
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem maxCap_attained {rs : List CapacityRecord} (hne : rs ≠ []) :
    ∃ r, r ∈ rs ∧ r.cap = maxCap rs := by
  induction rs with
  | nil => exact (hne rfl).elim
  | cons s ss ih =>
      cases ss with
      | nil =>
          refine ⟨s, by simp, ?_⟩
          simp [maxCap]
      | cons t ts =>
          by_cases hle : s.cap ≤ maxCap (t :: ts)
          · have hmax : max s.cap (maxCap (t :: ts)) = maxCap (t :: ts) :=
              Nat.max_eq_right hle
            obtain ⟨r, hr, hcap⟩ := ih (by simp)
            refine ⟨r, by simp [hr], ?_⟩
            change r.cap = max s.cap (maxCap (t :: ts))
            rw [hmax]
            exact hcap
          · have hlt : maxCap (t :: ts) < s.cap := Nat.lt_of_not_ge hle
            have hmax : max s.cap (maxCap (t :: ts)) = s.cap := by omega
            refine ⟨s, by simp, ?_⟩
            change s.cap = max s.cap (maxCap (t :: ts))
            rw [hmax]

/-- Records whose capacity reaches threshold `lam`. -/
def eligible (rs : List CapacityRecord) (lam : Nat) : List CapacityRecord :=
  rs.filter (fun r => decide (lam ≤ r.cap))

/-- Largest endpoint among records reaching threshold `lam`, or `-1` if none. -/
def latestAt (rs : List CapacityRecord) (lam : Nat) : Int :=
  ((eligible rs lam).map (fun r => (r.endpoint : Int))).foldr max (-1)

theorem endpoint_le_latestAt {r : CapacityRecord} {rs : List CapacityRecord}
    {lam : Nat} (hr : r ∈ rs) (hcap : lam ≤ r.cap) :
    (r.endpoint : Int) ≤ latestAt rs lam := by
  unfold latestAt eligible
  apply CutArith.le_foldr_max
  rw [List.mem_map]
  refine ⟨r, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨hr, by simp [hcap]⟩

theorem latestAt_attained {rs : List CapacityRecord} {lam : Nat}
    (h : ∃ r, r ∈ rs ∧ lam ≤ r.cap) :
    ∃ r, r ∈ rs ∧ lam ≤ r.cap ∧ latestAt rs lam = (r.endpoint : Int) := by
  have hne : (eligible rs lam).map (fun r => (r.endpoint : Int)) ≠ [] := by
    obtain ⟨r, hr, hcap⟩ := h
    intro hnil
    have hmem : (r.endpoint : Int) ∈
        (eligible rs lam).map (fun r => (r.endpoint : Int)) := by
      rw [List.mem_map]
      refine ⟨r, ?_, rfl⟩
      unfold eligible
      rw [List.mem_filter]
      exact ⟨hr, by simp [hcap]⟩
    rw [hnil] at hmem
    simp at hmem
  have hmem : latestAt rs lam ∈
      (eligible rs lam).map (fun r => (r.endpoint : Int)) := by
    unfold latestAt
    exact CutArith.foldr_max_mem _ hne (fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨r, _hr, rfl⟩ := hx
      omega)
  rw [List.mem_map] at hmem
  obtain ⟨r, hrElig, hrEq⟩ := hmem
  unfold eligible at hrElig
  rw [List.mem_filter] at hrElig
  obtain ⟨hr, hp⟩ := hrElig
  simp only [decide_eq_true_eq] at hp
  exact ⟨r, hr, hp, hrEq.symm⟩

/-- Pointwise maximum characterization of `latestAt`: every eligible record is
bounded by it, and the bound is attained whenever at least one eligible record
exists. -/
theorem latestAt_is_pointwise_max (rs : List CapacityRecord) (lam : Nat) :
    (∀ r, r ∈ rs → lam ≤ r.cap → (r.endpoint : Int) ≤ latestAt rs lam) ∧
      ((∃ r, r ∈ rs ∧ lam ≤ r.cap) →
        ∃ r, r ∈ rs ∧ lam ≤ r.cap ∧ latestAt rs lam = (r.endpoint : Int)) :=
  ⟨fun _ hr hcap => endpoint_le_latestAt hr hcap, fun h => latestAt_attained h⟩

/-- The global M0 route: capacity first, then endpoint. -/
def globalRoute (rs : List CapacityRecord) : Route :=
  rmaxList (rs.map CapacityRecord.toRoute)

/-- The explicit capacity-first winner. -/
def winnerRoute (rs : List CapacityRecord) : Route :=
  CutArith.mk (maxCap rs : Int) (latestAt rs (maxCap rs))

theorem valid_globalRoute (rs : List CapacityRecord) : Valid (globalRoute rs) := by
  unfold globalRoute
  apply valid_rmaxList
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨x, _hx, rfl⟩ := hr
  exact CapacityRecord.valid_toRoute x

theorem valid_winnerRoute (rs : List CapacityRecord) : Valid (winnerRoute rs) := by
  unfold winnerRoute
  apply CutArith.valid_mk
  unfold latestAt
  exact CutArith.neg_one_le_foldr_max _

theorem winnerRoute_len (rs : List CapacityRecord) :
    (winnerRoute rs).len = (maxCap rs : Int) := by
  unfold winnerRoute
  by_cases hzero : maxCap rs = 0
  · rw [hzero]
    simp [CutArith.mk_nonpos, unmatched]
  · have hpos : 0 < (maxCap rs : Int) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [CutArith.mk_pos _ _ hpos]

theorem toRoute_le_winnerRoute {r : CapacityRecord} {rs : List CapacityRecord}
    (hr : r ∈ rs) : rle r.toRoute (winnerRoute rs) := by
  have hcaple : r.cap ≤ maxCap rs := cap_le_maxCap hr
  by_cases hlt : r.cap < maxCap rs
  · left
    rw [winnerRoute_len]
    exact CapacityRecord.toRoute_len_lt_of_cap_lt hlt
  · have hcap : r.cap = maxCap rs :=
      Nat.le_antisymm hcaple (Nat.le_of_not_gt hlt)
    by_cases hzero : maxCap rs = 0
    · have hrzero : r.cap = 0 := by omega
      rw [CapacityRecord.toRoute_eq_unmatched_of_zero hrzero]
      have hwin : winnerRoute rs = unmatched := by
        unfold winnerRoute
        rw [hzero]
        exact CutArith.mk_nonpos 0 (latestAt rs 0) (by omega)
      rw [hwin]
      exact rle_refl unmatched
    · have hmpos : 0 < maxCap rs := Nat.pos_of_ne_zero hzero
      have hrpos : 0 < r.cap := by omega
      rw [CapacityRecord.toRoute_eq_of_pos hrpos]
      unfold winnerRoute
      rw [CutArith.mk_pos _ _ (by exact_mod_cast hmpos)]
      right
      constructor
      · change (r.cap : Int) = (maxCap rs : Int)
        exact_mod_cast hcap
      · apply endpoint_le_latestAt hr
        omega

/-- The global `rmaxList` winner is exactly the maximum capacity, with the
largest endpoint among all records attaining that capacity. -/
theorem globalRoute_eq_winnerRoute (rs : List CapacityRecord) :
    globalRoute rs = winnerRoute rs := by
  apply rle_antisymm
  · unfold globalRoute
    apply rmaxList_lub
    · exact valid_winnerRoute rs
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨x, hx, rfl⟩ := hr
      exact toRoute_le_winnerRoute hx
  · by_cases hzero : maxCap rs = 0
    · have hwin : winnerRoute rs = unmatched := by
        unfold winnerRoute
        rw [hzero]
        exact CutArith.mk_nonpos 0 (latestAt rs 0) (by omega)
      rw [hwin]
      exact valid_rle_unmatched (globalRoute rs) (valid_globalRoute rs)
    · have hne : rs ≠ [] := by
        intro hnil
        apply hzero
        rw [hnil]
        rfl
      obtain ⟨r0, hr0, hcap0⟩ := maxCap_attained hne
      obtain ⟨r, hr, hcap, hlatest⟩ := latestAt_attained
        (rs := rs) (lam := maxCap rs) ⟨r0, hr0, by omega⟩
      have hcap_eq : r.cap = maxCap rs :=
        Nat.le_antisymm (cap_le_maxCap hr) hcap
      apply rle_trans (winnerRoute rs) r.toRoute (globalRoute rs)
      · unfold winnerRoute
        rw [CutArith.mk_pos _ _ (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        rw [CapacityRecord.toRoute_eq_of_pos (by omega)]
        right
        constructor
        · change (maxCap rs : Int) = (r.cap : Int)
          exact_mod_cast hcap_eq.symm
        · rw [hlatest]
          exact Int.le_refl _
      · unfold globalRoute
        apply rle_rmaxList
        rw [List.mem_map]
        exact ⟨r, hr, rfl⟩

/-- Capacity tie-break boundary: when the maximum capacity is positive, the
global route's endpoint is the largest endpoint among maximum-capacity records. -/
theorem globalRoute_endpoint_eq_latestAt_of_pos (rs : List CapacityRecord)
    (hpos : 0 < maxCap rs) :
    (globalRoute rs).endpoint = latestAt rs (maxCap rs) := by
  rw [globalRoute_eq_winnerRoute]
  unfold winnerRoute
  rw [CutArith.mk_pos _ _ (by exact_mod_cast hpos)]

/-- Exact completeness boundary for a record set representing one dense row.

Every record points to a causal endpoint and stores the row value at that
endpoint; conversely, every causal endpoint is represented by at least one
record.  Duplicate representations are harmless because the first conjunct
forces them to carry the same capacity. -/
def CompleteAt (ell : Nat → Nat) (t : Nat) (rs : List CapacityRecord) : Prop :=
  (∀ r, r ∈ rs → r.endpoint < t ∧ r.cap = ell r.endpoint) ∧
    (∀ e, e < t → ∃ r, r ∈ rs ∧ r.endpoint = e)

/-- A generic upper-bound lemma for a `foldr max` over `Int`. -/
theorem foldr_max_le {l : List Int} {b b' : Int}
    (hb : b ≤ b') (h : ∀ x, x ∈ l → x ≤ b') :
    l.foldr max b ≤ b' := by
  induction l generalizing b with
  | nil => simpa using hb
  | cons x xs ih =>
      simp only [List.foldr_cons]
      have hxle := h x (by simp)
      have htail := ih (b := b) hb (fun y hy => h y (by simp [hy]))
      omega

/-- Under completeness, the maximum record capacity is the dense `L_base`. -/
theorem Lbase_eq_maxCap_of_complete {ell : Nat → Nat} {t : Nat}
    {rs : List CapacityRecord} (hcomplete : CompleteAt ell t rs) (ht : 0 < t) :
    QCut.Lbase (fun e => (ell e : Int)) t = (maxCap rs : Int) := by
  apply Int.le_antisymm
  · unfold QCut.Lbase
    apply foldr_max_le
    · omega
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [List.mem_range] at he
      obtain ⟨r, hr, hend⟩ := hcomplete.2 e he
      have hcap := (hcomplete.1 r hr).2
      have hcap_e : r.cap = ell e := by simpa [hend] using hcap
      have hle := cap_le_maxCap hr
      change (ell e : Int) ≤ (maxCap rs : Int)
      rw [← hcap_e]
      exact_mod_cast hle
  · obtain ⟨r0, hr0, _⟩ := hcomplete.2 0 ht
    have hne : rs ≠ [] := by
      intro hnil
      rw [hnil] at hr0
      simp at hr0
    obtain ⟨r, hr, hcapmax⟩ := maxCap_attained hne
    have hrt := (hcomplete.1 r hr).1
    have hcapeq := (hcomplete.1 r hr).2
    rw [← hcapmax, hcapeq]
    exact QCut.le_Lbase (fun e => (ell e : Int)) t r.endpoint hrt

/-- Under completeness, the record endpoint suffix maximum is exactly the
latest dense endpoint reaching a threshold. -/
theorem latestAt_eq_qcut_latest_of_complete {ell : Nat → Nat} {t : Nat}
    {rs : List CapacityRecord} {lam : Nat} (hcomplete : CompleteAt ell t rs) :
    latestAt rs lam = QCut.latest (fun e => (ell e : Int)) t (lam : Int) := by
  apply Int.le_antisymm
  · unfold latestAt
    apply foldr_max_le
    · exact CutArith.neg_one_le_foldr_max _
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨r, hrElig, rfl⟩ := hx
      unfold eligible at hrElig
      rw [List.mem_filter] at hrElig
      obtain ⟨hr, hp⟩ := hrElig
      simp only [decide_eq_true_eq] at hp
      have hrt := (hcomplete.1 r hr).1
      have hcap := (hcomplete.1 r hr).2
      apply QCut.le_latest
      rw [QCut.mem_latestList]
      refine ⟨hrt, ?_⟩
      rw [← hcap]
      exact_mod_cast hp
  · unfold QCut.latest
    apply foldr_max_le
    · unfold latestAt
      exact CutArith.neg_one_le_foldr_max _
    · intro x hx
      unfold QCut.latestList at hx
      rw [List.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [List.mem_filter] at he
      obtain ⟨herange, hle⟩ := he
      rw [List.mem_range] at herange
      simp only [decide_eq_true_eq] at hle
      obtain ⟨r, hr, hend⟩ := hcomplete.2 e herange
      have hcap := (hcomplete.1 r hr).2
      have hlamr : lam ≤ r.cap := by
        have hnat : lam ≤ ell e := by exact_mod_cast hle
        rw [hcap]
        simpa [hend] using hnat
      rw [← hend]
      exact endpoint_le_latestAt hr hlamr

/-- A threshold query route: the requested cut length, with the latest eligible
record endpoint.  A zero length is normalized by `CutArith.mk`. -/
def thresholdRoute (rs : List CapacityRecord) (lam : Nat) : Route :=
  CutArith.mk (lam : Int) (latestAt rs lam)

/-- **Q-cut bridge.**  For a complete record set, `QCut.qcutClosed` is exactly
the record-level threshold query at `min (max capacity) (t-u)`. -/
theorem qcutClosed_eq_thresholdRoute_of_complete {ell : Nat → Nat}
    {t u : Nat} {rs : List CapacityRecord} (hcomplete : CompleteAt ell t rs)
    (ht : 0 < t) (hu : u ≤ t) :
    QCut.qcutClosed (fun e => (ell e : Int)) t u =
      thresholdRoute rs (min (maxCap rs) (t - u)) := by
  unfold QCut.qcutClosed thresholdRoute
  rw [QCut.qcutLambda_eq (ell := fun e => (ell e : Int)) (by omega)]
  rw [Lbase_eq_maxCap_of_complete hcomplete ht]
  have hsub : ((t : Int) - (u : Int)) = ((t - u : Nat) : Int) := by omega
  rw [hsub]
  have hmin : min (maxCap rs : Int) ((t - u : Nat) : Int) =
      ((min (maxCap rs) (t - u) : Nat) : Int) := by omega
  rw [hmin]
  rw [latestAt_eq_qcut_latest_of_complete hcomplete]


/-! ### Rectangle records and multi-run gluing -/

/-- The ordinary and feasible spike records emitted by one active same-symbol
K-run rectangle. -/
def rectangleRecords (c d x gamma : Nat) : List CapacityRecord :=
  ⟨ordinaryCap x (d - c + 1), d⟩ ::
    if spikeEndpoint c x ≤ d then
      [⟨spikeCap x gamma, spikeEndpoint c x⟩]
    else
      []

theorem valid_ordinaryRecord {c d x : Nat} (_hcd : c ≤ d) (hx : 0 < x) :
    Valid (ordinaryRecord c d x) := by
  unfold ordinaryRecord ordinaryCap
  apply CutArith.valid_pair
  · change (0 : Int) < ((min x (d - c + 1) : Nat) : Int)
    omega
  · omega

theorem valid_spikeRecord {c d x gamma : Nat} (hx : 0 < x) :
    Valid (spikeRecord c d x gamma) := by
  unfold spikeRecord spikeEndpoint spikeCap
  by_cases hp : c + x - 1 ≤ d
  · rw [if_pos hp]
    apply CutArith.valid_pair
    · change (0 : Int) < ((x + gamma : Nat) : Int)
      omega
    · omega
  · rw [if_neg hp]
    exact valid_unmatched

theorem rmaxList_singleton_of_valid (a : Route) (ha : Valid a) :
    rmaxList [a] = a := by
  simp only [rmaxList]
  exact rmax_unmatched_right a ha

theorem rmaxList_pair_of_valid_right (a b : Route) (hb : Valid b) :
    rmaxList [a, b] = rmax a b := by
  simp only [rmaxList]
  rw [rmax_unmatched_right b hb]

/-- The ordinary/spike capacity records of one rectangle have exactly the
`rmax` of the two headline records as their aggregate route. -/
theorem rectangleRecords_rmax_eq_two_records {c d x gamma : Nat}
    (hcd : c ≤ d) (hx : 0 < x) :
    rmaxList ((rectangleRecords c d x gamma).map CapacityRecord.toRoute) =
      rmax (ordinaryRecord c d x) (spikeRecord c d x gamma) := by
  have hordcap : 0 < ordinaryCap x (d - c + 1) := by
    unfold ordinaryCap
    omega
  have hordto :
      CapacityRecord.toRoute ⟨ordinaryCap x (d - c + 1), d⟩ =
        ordinaryRecord c d x := by
    unfold CapacityRecord.toRoute ordinaryRecord
    rw [CutArith.mk_pos _ _ (by exact_mod_cast hordcap)]
  by_cases hp : spikeEndpoint c x ≤ d
  · have hspikepos : 0 < spikeCap x gamma := by
      unfold spikeCap
      omega
    have hp' : c + x - 1 ≤ d := by simpa [spikeEndpoint] using hp
    have hspto :
        CapacityRecord.toRoute ⟨spikeCap x gamma, spikeEndpoint c x⟩ =
          spikeRecord c d x gamma := by
      unfold CapacityRecord.toRoute spikeRecord spikeCap spikeEndpoint
      rw [if_pos hp', CutArith.mk_pos _ _ (by exact_mod_cast hspikepos)]
    unfold rectangleRecords
    rw [if_pos hp]
    simp only [List.map_cons, List.map_nil]
    rw [hordto, hspto]
    exact rmaxList_pair_of_valid_right _ _ (valid_spikeRecord hx)
  · unfold rectangleRecords
    rw [if_neg hp]
    simp only [List.map_cons, List.map_nil]
    rw [hordto]
    unfold spikeRecord
    rw [if_neg hp]
    have hordvalid := valid_ordinaryRecord hcd hx
    rw [rmax_unmatched_right _ hordvalid]
    exact rmaxList_singleton_of_valid _ hordvalid

/-- Flattening blocks of valid routes commutes with `rmaxList`: the global
winner is the winner of the per-block winners. -/
theorem rmaxList_flatten_eq_rmaxList_map {blocks : List (List Route)}
    (hvalid : ∀ r, r ∈ blocks.flatten → Valid r) :
    rmaxList blocks.flatten = rmaxList (blocks.map rmaxList) := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
      rw [List.flatten_cons]
      rw [rmaxList_append b bs.flatten (fun r hr => hvalid r (by simp [hr]))]
      rw [ih (fun r hr => hvalid r (by simp [hr]))]
      rfl

/-- One active run rectangle, carrying only the parameters needed by its two
capacity records. -/
structure RunCandidate where
  c : Nat
  d : Nat
  x : Nat
  gamma : Nat

/-- All records emitted by a run. -/
def runRecords (R : RunCandidate) : List CapacityRecord :=
  rectangleRecords R.c R.d R.x R.gamma

/-- The per-run winner after the ordinary/spike reduction. -/
def runRoute (R : RunCandidate) : Route :=
  rmax (ordinaryRecord R.c R.d R.x) (spikeRecord R.c R.d R.x R.gamma)

/-- The record union over multiple runs. -/
def multiRunRecords (runs : List RunCandidate) : List CapacityRecord :=
  (runs.map runRecords).flatten

/-- The per-run `rmax` reduction of the same multi-run family. -/
def multiRunRoute (runs : List RunCandidate) : Route :=
  rmaxList (runs.map runRoute)

/-- Multi-run aggregation: flattening all ordinary/spike records gives exactly
the `rmaxList` of the per-run two-record winners. -/
theorem multiRunRecords_eq_per_run (runs : List RunCandidate)
    (hvalid : ∀ R, R ∈ runs → R.c ≤ R.d ∧ 0 < R.x) :
    rmaxList ((multiRunRecords runs).map CapacityRecord.toRoute) =
      multiRunRoute runs := by
  unfold multiRunRecords multiRunRoute
  rw [List.map_flatten]
  rw [rmaxList_flatten_eq_rmaxList_map]
  · congr 1
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro R hR
    exact rectangleRecords_rmax_eq_two_records (hvalid R hR).1 (hvalid R hR).2
  · intro r hr
    rw [List.mem_flatten] at hr
    obtain ⟨block, hblock, hrblock⟩ := hr
    rw [List.mem_map] at hblock
    obtain ⟨R, _hR, rfl⟩ := hblock
    rw [List.mem_map] at hrblock
    obtain ⟨rec, _hrec, rfl⟩ := hrblock
    exact CapacityRecord.valid_toRoute rec

/-- Cross-run capacity tie-break: at positive maximum capacity, the global
multi-run route endpoint is the largest endpoint among all maximum-capacity
records across runs. -/
theorem multiRun_endpoint_eq_latestAt_of_pos (runs : List RunCandidate)
    (hpos : 0 < maxCap (multiRunRecords runs)) :
    (rmaxList ((multiRunRecords runs).map CapacityRecord.toRoute)).endpoint =
      latestAt (multiRunRecords runs) (maxCap (multiRunRecords runs)) :=
  globalRoute_endpoint_eq_latestAt_of_pos (multiRunRecords runs) hpos


end CapacityMultiRun

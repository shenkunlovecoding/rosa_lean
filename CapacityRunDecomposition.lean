import CapacityConcrete

/-!
## Capacity row-cover run decompositions

`CapacityConcrete.RowCovered` is the concrete boundary consumed by the
multi-run capacity/Q-cut bridge.  This file packages that boundary as a
reusable decomposition object:

* `RunCover` records soundness (`R.d < t`) and completeness (every endpoint
  `e < t` lies in one of the maximal `RealRun` rectangles);
* `RunDecomposition` additionally records that every causal endpoint is
  assigned to a *unique* run interval.  Adjacent integer intervals are
  allowed: for example `[0,0]` and `[1,1]` are disjoint endpoint intervals.

No string-level maximal-run enumeration is required.  A concrete enumerator
can construct a `RunCover`/`RunDecomposition`, while all downstream users only
need the resulting `CapacityConcrete.RowCovered` proof.
-/

open Route
open Capacity
open Lcs
open CapacityMultiRun
open RunRect
open CapacityConcrete

namespace CapacityRunDecomposition

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α]
variable {q k : Nat → α} {Tq Tk t : Nat}

/-- Sound and complete coverage of the causal row `[0,t)` by maximal
equal-symbol `RealRun` rectangles. -/
structure RunCover (q : Nat → α) (k : Nat → α) (Tq Tk t : Nat) where
  /-- The maximal constant-run rectangles used by the capacity layer. -/
  runs : List (RealRun q k Tq Tk t)
  /-- Every run is causal: its K-run endpoint is before the row position. -/
  ends_before : ∀ R, R ∈ runs → R.d < t
  /-- Every causal endpoint is covered by at least one run. -/
  covers : ∀ e, e < t → ∃ R, R ∈ runs ∧ R.c ≤ e ∧ e ≤ R.d

namespace RunCover

/-- A `RunCover` is exactly the existing concrete `RowCovered` boundary. -/
theorem toRowCovered (D : RunCover q k Tq Tk t) : RowCovered D.runs :=
  ⟨D.ends_before, D.covers⟩

/-- Soundness projection. -/
theorem sound (D : RunCover q k Tq Tk t) :
    ∀ R, R ∈ D.runs → R.d < t :=
  D.ends_before

/-- Completeness projection. -/
theorem complete (D : RunCover q k Tq Tk t) :
    ∀ e, e < t → ∃ R, R ∈ D.runs ∧ R.c ≤ e ∧ e ≤ R.d :=
  D.covers

/-- A sound/complete run cover discharges `CapacityConcrete.RowCovered`. -/
theorem rowCovered (D : RunCover q k Tq Tk t) : RowCovered D.runs :=
  D.toRowCovered

/-- The exact endpoint records contributed by a run cover are complete. -/
theorem completeAt_multiEndpointRecords (D : RunCover q k Tq Tk t) :
    CapacityMultiRun.CompleteAt (fun e => lcsLen q k t e) t
      (multiEndpointRecords D.runs) :=
  CapacityConcrete.completeAt_multiEndpointRecords_of_rowCovered D.toRowCovered

/-- The exact endpoint-record Q-cut bridge with the row-cover hypothesis
discharged by a sound/complete `RunCover`. -/
theorem qcutClosed_eq_thresholdRoute_multiEndpointRecords
    (D : RunCover q k Tq Tk t) {u : Nat} (ht : 0 < t) (hu : u ≤ t) :
    QCut.qcutClosed (fun e => (lcsLen q k t e : Int)) t u =
      CapacityMultiRun.thresholdRoute (multiEndpointRecords D.runs)
        (min (CapacityMultiRun.maxCap (multiEndpointRecords D.runs)) (t - u)) :=
  CapacityConcrete.qcutClosed_eq_thresholdRoute_multiEndpointRecords_of_rowCovered
    D.toRowCovered ht hu

/-- The compressed capacity-record Q-cut bridge with the row-cover hypothesis
discharged by a sound/complete `RunCover`. -/
theorem qcutClosed_eq_thresholdRoute_multiCapacityRecords
    (D : RunCover q k Tq Tk t) {u : Nat} (ht : 0 < t) (hu : u ≤ t) :
    QCut.qcutClosed (fun e => (lcsLen q k t e : Int)) t u =
      CapacityMultiRun.thresholdRoute (multiCapacityRecords D.runs)
        (min (CapacityMultiRun.maxCap (multiCapacityRecords D.runs)) (t - u)) :=
  CapacityConcrete.qcutClosed_eq_thresholdRoute_multiCapacityRecords_of_rowCovered
    D.toRowCovered ht hu

end RunCover

/-- A genuine endpoint decomposition of the causal row.  On top of `RunCover`,
each endpoint is contained in exactly one run interval. -/
structure RunDecomposition (q : Nat → α) (k : Nat → α) (Tq Tk t : Nat)
    extends RunCover q k Tq Tk t where
  /-- Every causal endpoint has a unique containing run. -/
  assigned : ∀ e, e < t →
    ∃ R, (R ∈ runs ∧ R.c ≤ e ∧ e ≤ R.d) ∧
      ∀ S, (S ∈ runs ∧ S.c ≤ e ∧ e ≤ S.d) → S = R

namespace RunDecomposition

/-- Forget exact endpoint assignment and retain only sound/complete coverage. -/
def forget (D : RunDecomposition q k Tq Tk t) : RunCover q k Tq Tk t :=
  { runs := D.runs
    ends_before := D.ends_before
    covers := D.covers }

/-- A `RunDecomposition` is exactly the existing concrete `RowCovered`
boundary after forgetting uniqueness. -/
theorem toRowCovered (D : RunDecomposition q k Tq Tk t) : RowCovered D.runs :=
  D.forget.toRowCovered

/-- Exact endpoint assignment projection. -/
theorem complete_exact (D : RunDecomposition q k Tq Tk t) :
    ∀ e, e < t → ∃ R, (R ∈ D.runs ∧ R.c ≤ e ∧ e ≤ R.d) ∧
      ∀ S, (S ∈ D.runs ∧ S.c ≤ e ∧ e ≤ S.d) → S = R :=
  D.assigned

/-- A run decomposition discharges `CapacityConcrete.RowCovered`. -/
theorem rowCovered (D : RunDecomposition q k Tq Tk t) : RowCovered D.runs :=
  D.toRowCovered

/-- Build a decomposition from the existing row-cover boundary and a proof
that endpoint assignments are unique. -/
def ofRowCovered (runs : List (RealRun q k Tq Tk t)) (hcover : RowCovered runs)
    (hunique : ∀ e, e < t →
      ∃ R, (R ∈ runs ∧ R.c ≤ e ∧ e ≤ R.d) ∧
      ∀ S, (S ∈ runs ∧ S.c ≤ e ∧ e ≤ S.d) → S = R) :
    RunDecomposition q k Tq Tk t where
  runs := runs
  ends_before := hcover.1
  covers := hcover.2
  assigned := hunique

/-- The exact endpoint records contributed by a decomposition are complete. -/
theorem completeAt_multiEndpointRecords (D : RunDecomposition q k Tq Tk t) :
    CapacityMultiRun.CompleteAt (fun e => lcsLen q k t e) t
      (multiEndpointRecords D.runs) :=
  CapacityConcrete.completeAt_multiEndpointRecords_of_rowCovered D.toRowCovered

/-- The exact endpoint-record Q-cut bridge with the row-cover hypothesis
discharged by a `RunDecomposition`. -/
theorem qcutClosed_eq_thresholdRoute_multiEndpointRecords
    (D : RunDecomposition q k Tq Tk t) {u : Nat} (ht : 0 < t) (hu : u ≤ t) :
    QCut.qcutClosed (fun e => (lcsLen q k t e : Int)) t u =
      CapacityMultiRun.thresholdRoute (multiEndpointRecords D.runs)
        (min (CapacityMultiRun.maxCap (multiEndpointRecords D.runs)) (t - u)) :=
  CapacityConcrete.qcutClosed_eq_thresholdRoute_multiEndpointRecords_of_rowCovered
    D.toRowCovered ht hu

/-- The compressed capacity-record Q-cut bridge with the row-cover hypothesis
discharged by a `RunDecomposition`. -/
theorem qcutClosed_eq_thresholdRoute_multiCapacityRecords
    (D : RunDecomposition q k Tq Tk t) {u : Nat} (ht : 0 < t) (hu : u ≤ t) :
    QCut.qcutClosed (fun e => (lcsLen q k t e : Int)) t u =
      CapacityMultiRun.thresholdRoute (multiCapacityRecords D.runs)
        (min (CapacityMultiRun.maxCap (multiCapacityRecords D.runs)) (t - u)) :=
  CapacityConcrete.qcutClosed_eq_thresholdRoute_multiCapacityRecords_of_rowCovered
    D.toRowCovered ht hu

end RunDecomposition

/-- Either a sound/complete cover or an exact decomposition discharges the
`RowCovered` input of the capacity multi-run bridge. -/
theorem rowCovered_of_runCover (D : RunCover q k Tq Tk t) : RowCovered D.runs :=
  D.rowCovered

/-- Exact-decomposition version of `rowCovered_of_runCover`. -/
theorem rowCovered_of_runDecomposition (D : RunDecomposition q k Tq Tk t) :
    RowCovered D.runs :=
  D.rowCovered

end CapacityRunDecomposition

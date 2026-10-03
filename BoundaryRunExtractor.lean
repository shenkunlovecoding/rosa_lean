import BoundaryRecursive

/-!
## Finite run-list extraction and boundary singleton closure

`BoundaryRecursive` packages one singleton next-run step as an `RSP` shape, but it
leaves the list of runs implicit.  This file makes that list explicit.

* `Run` is a maximal constant run together with its maximality proof.
* `RunSeq` is a finite, adjacent, cover-complete run decomposition.
* `extractRunSeq` constructs such a decomposition for every finite string,
  using a structural fuel recursion (no termination axiom).
* `rightCertificateOfRun` and `topCertificateOfRun` consume the finite suffix
  after a run and close all singleton/mismatch cases.
* `BoundaryWindow` assembles the resulting four edge certificates directly as a
  `BoundaryRspCertificate`, hence inherits the seven-range bound.

The string endpoints are handled explicitly.  If the singleton next run is the
last run, the open edge is zero.  A full six-run `BoundaryWindow` still needs a
previous run on each side; that condition is recorded in the final report.
-/

open Lcs RunRect Repair RspSummary
open BoundaryRangeCount
open BoundaryZeroCertificates
open BoundaryRecursive

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace BoundaryRunExtractor

variable {α : Type} [DecidableEq α]

/-! ### Maximal runs and finite run lists -/

/-- A maximal constant run of a finite functional string. -/
structure Run (s : Nat → α) (T : Nat) where
  lo : Nat
  hi : Nat
  sym : α
  nonempty : lo ≤ hi
  maximal : ConstRun s T lo hi sym

/-- A finite adjacent run decomposition starting at `lo`.

`RunSeq.nil` is the string-end base case; `RunSeq.cons` exposes the strict
advance `r.lo = lo` and continues at `r.hi + 1`. -/
inductive RunSeq (s : Nat → α) (T : Nat) : Nat → List (Run s T) → Prop
  | nil {lo : Nat} (h : lo = T) : RunSeq s T lo []
  | cons {lo : Nat} (r : Run s T) {rs : List (Run s T)}
      (hlo : r.lo = lo) (htail : RunSeq s T (r.hi + 1) rs) :
      RunSeq s T lo (r :: rs)

/-! ### Extraction of one maximal run -/

/-- Extend a constant prefix from `lo` while the next symbol equals `sym`.
Fuel is just the number of symbols that may be inspected; it never acts as an
axiom. -/
def extendRunHi (s : Nat → α) (T : Nat) (sym : α) : Nat → Nat → Nat
  | lo, 0 => lo
  | lo, fuel + 1 =>
      if _h : lo + 1 < T then
        if s (lo + 1) = sym then
          extendRunHi s T sym (lo + 1) fuel
        else lo
      else lo

/-- Correctness of `extendRunHi`: it returns a maximal constant prefix (up to
the supplied fuel bound) with the requested symbol. -/
theorem extendRunHi_spec (s : Nat → α) (T : Nat) (sym : α) :
    ∀ fuel lo, sym = s lo → lo < T → T - lo - 1 ≤ fuel →
      let hi := extendRunHi s T sym lo fuel
      lo ≤ hi ∧ hi < T ∧
      (∀ x, lo ≤ x → x ≤ hi → s x = sym) ∧
      (hi + 1 < T → s (hi + 1) ≠ sym) := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hsym hlo hfuel
      simp only [extendRunHi]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro x hxlo hxhi
        have hx : x = lo := by omega
        subst x
        exact hsym.symm
      · intro hnext
        omega
  | succ fuel ih =>
      intro lo hsym hlo hfuel
      by_cases hnext : lo + 1 < T
      · by_cases heq : s (lo + 1) = sym
        · have hfuel' : T - (lo + 1) - 1 ≤ fuel := by omega
          have hsym' : sym = s (lo + 1) := heq.symm
          have hspec := ih (lo + 1) hsym' (by omega) hfuel'
          have hred : extendRunHi s T sym lo (fuel + 1) =
              extendRunHi s T sym (lo + 1) fuel := by
            simp [extendRunHi, hnext, heq]
          rw [hred]
          dsimp only at hspec
          rcases hspec with ⟨hle, hlt, hmem, hright⟩
          refine ⟨by omega, hlt, ?_, ?_⟩
          · intro x hxl hxh
            by_cases hx : x = lo
            · subst x
              exact hsym.symm
            · have hxlo1 : lo + 1 ≤ x := by omega
              exact hmem x hxlo1 hxh
          · intro hnext2
            exact hright hnext2
        · have hred : extendRunHi s T sym lo (fuel + 1) = lo := by
            simp [extendRunHi, hnext, heq]
          rw [hred]
          refine ⟨Nat.le_refl lo, by omega, ?_, ?_⟩
          · intro x hxl hxh
            have hx : x = lo := by omega
            subst x
            exact hsym.symm
          · intro hnext2
            exact heq
      · have hred : extendRunHi s T sym lo (fuel + 1) = lo := by
          simp [extendRunHi, hnext]
        rw [hred]
        refine ⟨Nat.le_refl lo, hlo, ?_, ?_⟩
        · intro x hxl hxh
          have hx : x = lo := by omega
          subst x
          exact hsym.symm
        · intro hnext2
          omega

/-- Structural extraction of a complete run sequence.  The fuel is reduced at
every emitted run, while `lo ≤ T` and `T - lo ≤ fuel` are maintained as
invariants. -/
def extractRunSeq (s : Nat → α) (T : Nat) :
    (fuel lo : Nat) → (lo = 0 ∨ (0 < lo ∧ s (lo - 1) ≠ s lo)) →
      lo ≤ T → T - lo ≤ fuel → { runs : List (Run s T) // RunSeq s T lo runs }
  | 0, lo, _hstart, hle, _hrem => by
      have hlo : lo = T := by omega
      exact ⟨[], RunSeq.nil hlo⟩
  | fuel + 1, lo, hstart, hle, hrem => by
      by_cases hlt : lo < T
      · let sym := s lo
        let hi := extendRunHi s T sym lo (T - lo - 1)
        have hspec : lo ≤ hi ∧ hi < T ∧
            (∀ x, lo ≤ x → x ≤ hi → s x = sym) ∧
            (hi + 1 < T → s (hi + 1) ≠ sym) := by
          dsimp [hi]
          exact extendRunHi_spec s T sym (T - lo - 1) lo rfl hlt (Nat.le_refl _)
        let run : Run s T := {
          lo := lo
          hi := hi
          sym := sym
          nonempty := hspec.1
          maximal := {
            hi_lt := hspec.2.1
            mem := hspec.2.2.1
            left_ne := by
              intro hpos
              rcases hstart with hzero | hprev
              · omega
              · exact hprev.2
            right_ne := hspec.2.2.2
          }
        }
        by_cases hnext : hi + 1 < T
        · have hstart' : hi + 1 = 0 ∨
              (0 < hi + 1 ∧ s (hi + 1 - 1) ≠ s (hi + 1)) := by
            right
            constructor
            · omega
            · have hsh : s hi = sym := hspec.2.2.1 hi (by omega) (Nat.le_refl hi)
              intro heq
              exact hspec.2.2.2 hnext (heq.symm.trans hsh)
          let tail := extractRunSeq s T fuel (hi + 1) hstart' (by omega) (by omega)
          exact ⟨run :: tail.1, RunSeq.cons run rfl tail.2⟩
        · have hend : hi + 1 = T := by omega
          exact ⟨[run], RunSeq.cons run rfl (RunSeq.nil hend)⟩
      · have hlo : lo = T := by omega
        exact ⟨[], RunSeq.nil hlo⟩

/-- The canonical finite run decomposition of `s[0..T)`. -/
def fullRunList (s : Nat → α) (T : Nat) : List (Run s T) :=
  (extractRunSeq s T T 0 (Or.inl rfl) (Nat.zero_le T) (Nat.le_refl T)).1

/-- `fullRunList` is cover-complete and adjacent. -/
theorem fullRunList_sound (s : Nat → α) (T : Nat) :
    RunSeq s T 0 (fullRunList s T) :=
  (extractRunSeq s T T 0 (Or.inl rfl) (Nat.zero_le T) (Nat.le_refl T)).2

/-! ### Right edge: singleton suffixes -/

/-- Direct right-edge certificate for all non-degenerate cases: equal symbols,
a non-singleton current run, or a singleton opposite run. -/
def rightDirectCertificate
    {q k : Nat → α} {Tq Tk : Nat} (K : Run k Tk) (r : Run q Tq)
    (hcase : r.sym = K.sym ∨ r.lo < r.hi ∨ K.lo = K.hi) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk r.lo (K.hi - z)) := by
  by_cases hsame : r.sym = K.sym
  · exact rightEdgeCertificateGuarded r.maximal K.maximal hsame r.nonempty K.nonempty
  · by_cases hnon : r.lo < r.hi
    · exact rightCertificateOrCornerSpike r.maximal K.maximal
        (by intro _; exact hnon) r.nonempty K.nonempty
    · have hks : K.lo = K.hi := by
        rcases hcase with hsame' | hrest
        · exact False.elim (hsame hsame')
        · rcases hrest with hnon' | hks
          · omega
          · exact hks
      exact rightCertificateOrCornerSpike r.maximal K.maximal
        (by intro hk; omega) r.nonempty K.nonempty


/-- Right-edge certificate obtained from the first run and the complete suffix
after it.  Non-singleton and same-symbol cases are direct.  In the remaining
singleton/mismatch case the next run either ends the string, mismatches the
opposite symbol, or supplies the one-step recursive certificate. -/
def rightCertificateOfRun
    {q k : Nat → α} {Tq Tk : Nat} (K : Run k Tk) (r : Run q Tq)
    (rs : List (Run q Tq)) (hseq : RunSeq q Tq (r.hi + 1) rs) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk r.lo (K.hi - z)) := by
  by_cases hsame : r.sym = K.sym
  · exact rightEdgeCertificateGuarded r.maximal K.maximal hsame r.nonempty K.nonempty
  · by_cases hnon : r.lo < r.hi
    · exact rightCertificateOrCornerSpike r.maximal K.maximal
        (by intro _; exact hnon) r.nonempty K.nonempty
    · by_cases hks : K.lo = K.hi
      · exact rightCertificateOrCornerSpike r.maximal K.maximal
          (by intro hk; omega) r.nonempty K.nonempty
      · have hsingle : r.lo = r.hi :=
          Nat.le_antisymm r.nonempty (Nat.le_of_not_gt hnon)
        cases rs with
        | nil =>
            have hend : r.hi + 1 = Tq := by
              cases hseq with
              | nil h => exact h
            have hm := r.maximal
            rw [← hsingle] at hm
            have hmaxSingleton : ConstRun q Tq r.lo r.lo r.sym := hm
            have hend' : r.lo + 1 = Tq := by omega
            exact rightSingletonEndCertificate hmaxSingleton hend' K.maximal K.nonempty
        | cons r' rs' =>
            have hlo : r'.lo = r.hi + 1 := by
              cases hseq with
              | cons _ hlo _ => exact hlo
            have hnextMax : ConstRun q Tq (r.lo + 1) r'.hi r'.sym := by
              simpa [hsingle, hlo] using r'.maximal
            have hm := r.maximal
            rw [← hsingle] at hm
            have hmaxSingleton : ConstRun q Tq r.lo r.lo r.sym := hm
            have hlo' : r.lo + 1 = r'.lo := by
              rw [hlo, hsingle]
            have hnext_nonempty : r.lo + 1 ≤ r'.hi := by
              simpa [hlo'] using r'.nonempty
            by_cases hnextsame : r'.sym = K.sym
            · have hnextMaxK : ConstRun q Tq (r.lo + 1) r'.hi K.sym := by
                simpa [hnextsame] using hnextMax
              exact rightSingletonRecursiveCertificate hmaxSingleton hnextMaxK
                hnext_nonempty K.maximal K.nonempty
            · exact rightSingletonMismatchZeroCertificate hmaxSingleton hnextMax
                hnext_nonempty K.maximal K.nonempty hnextsame

/-- Every run in a complete adjacent sequence has a complete suffix after it.
This is the index-selection lemma used to apply the right/top scanners to any
finite-string run. -/
theorem RunSeq.exists_suffix_of_mem
    {s : Nat → α} {T lo : Nat} {runs : List (Run s T)} {r : Run s T}
    (h : RunSeq s T lo runs) (hr : r ∈ runs) :
    ∃ rs, RunSeq s T (r.hi + 1) rs := by
  induction h with
  | nil => simp at hr
  | cons r0 hlo htail ih =>
      simp only [List.mem_cons] at hr
      rcases hr with hr | hr
      · subst hr
        exact ⟨_, htail⟩
      · exact ih hr

/-- The right-edge certificate exists for any run appearing in a complete finite
run sequence.  The suffix supplied to the scanner is obtained from the sequence
itself, so no termination fact is assumed. -/
theorem rightCertificateOfMembership
    {q k : Nat → α} {Tq Tk : Nat} {runs : List (Run q Tq)} {r : Run q Tq}
    (K : Run k Tk) (hQ : RunSeq q Tq 0 runs) (hr : r ∈ runs) :
    ∃ rs, ∃ hseq : RunSeq q Tq (r.hi + 1) rs,
      Nonempty (EdgeRspCertificate (fun z => lcpLen q k Tq Tk r.lo (K.hi - z))) := by
  obtain ⟨rs, hseq⟩ := RunSeq.exists_suffix_of_mem hQ hr
  exact ⟨rs, hseq, ⟨rightCertificateOfRun K r rs hseq⟩⟩

/-- String-level right-edge closure: every run in the canonical finite
decomposition admits a right-edge certificate against any fixed K-run. -/
theorem rightCertificateOfStringRun
    {q k : Nat → α} {Tq Tk : Nat} (K : Run k Tk) (r : Run q Tq)
    (hr : r ∈ fullRunList q Tq) :
    ∃ rs, ∃ hseq : RunSeq q Tq (r.hi + 1) rs,
      Nonempty (EdgeRspCertificate (fun z => lcpLen q k Tq Tk r.lo (K.hi - z))) :=
  rightCertificateOfMembership K (fullRunList_sound q Tq) hr

/-- Direct top-edge certificate for the non-degenerate cases. -/
def topDirectCertificate
    {q k : Nat → α} {Tq Tk : Nat} (Q : Run q Tq) (r : Run k Tk)
    (hcase : r.sym = Q.sym ∨ r.lo < r.hi ∨ Q.lo = Q.hi) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (Q.hi - z) r.lo) := by
  by_cases hsame : r.sym = Q.sym
  · exact BoundaryCertificates.top_edge_certificate Q.maximal r.maximal
      hsame.symm Q.nonempty r.nonempty
  · by_cases hnon : r.lo < r.hi
    · exact topCertificateOrCornerSpike Q.maximal r.maximal
        (by intro _; exact hnon) Q.nonempty r.nonempty
    · have hqs : Q.lo = Q.hi := by
        rcases hcase with hsame' | hrest
        · exact False.elim (hsame hsame')
        · rcases hrest with hnon' | hqs
          · omega
          · exact hqs
      exact topCertificateOrCornerSpike Q.maximal r.maximal
        (by intro hq; omega) Q.nonempty r.nonempty

/-- Top-edge certificate obtained from the first K run and the complete suffix
after it.  This is the reflected analogue of `rightCertificateOfRun`. -/
def topCertificateOfRun
    {q k : Nat → α} {Tq Tk : Nat} (Q : Run q Tq) (r : Run k Tk)
    (rs : List (Run k Tk)) (hseq : RunSeq k Tk (r.hi + 1) rs) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (Q.hi - z) r.lo) := by
  by_cases hsame : r.sym = Q.sym
  · exact BoundaryCertificates.top_edge_certificate Q.maximal r.maximal
      hsame.symm Q.nonempty r.nonempty
  · by_cases hnon : r.lo < r.hi
    · exact topCertificateOrCornerSpike Q.maximal r.maximal
        (by intro _; exact hnon) Q.nonempty r.nonempty
    · by_cases hqs : Q.lo = Q.hi
      · exact topCertificateOrCornerSpike Q.maximal r.maximal
          (by intro hq; omega) Q.nonempty r.nonempty
      · have hsingle : r.lo = r.hi :=
          Nat.le_antisymm r.nonempty (Nat.le_of_not_gt hnon)
        cases rs with
        | nil =>
            have hend : r.hi + 1 = Tk := by
              cases hseq with
              | nil h => exact h
            have hr := r.maximal
            rw [← hsingle] at hr
            have hmaxSingleton : ConstRun k Tk r.lo r.lo r.sym := hr
            have hend' : r.lo + 1 = Tk := by omega
            exact topSingletonEndCertificate Q.maximal Q.nonempty hmaxSingleton hend'
        | cons r' rs' =>
            have hlo : r'.lo = r.hi + 1 := by
              cases hseq with
              | cons _ hlo _ => exact hlo
            have hn := r'.maximal
            rw [hlo, ← hsingle] at hn
            have hnextMax : ConstRun k Tk (r.lo + 1) r'.hi r'.sym := hn
            have hr := r.maximal
            rw [← hsingle] at hr
            have hmaxSingleton : ConstRun k Tk r.lo r.lo r.sym := hr
            have hlo' : r.lo + 1 = r'.lo := by
              rw [hlo, hsingle]
            have hnext_nonempty : r.lo + 1 ≤ r'.hi := by
              simpa [hlo'] using r'.nonempty
            by_cases hnextsame : r'.sym = Q.sym
            · have hnextMaxQ : ConstRun k Tk (r.lo + 1) r'.hi Q.sym := by
                simpa [hnextsame] using hnextMax
              exact topSingletonRecursiveCertificate Q.maximal Q.nonempty
                hmaxSingleton hnextMaxQ hnext_nonempty
            · exact topSingletonMismatchZeroCertificate Q.maximal Q.nonempty
                hmaxSingleton hnextMax hnext_nonempty hnextsame

/-- The top-edge certificate exists for any K-run appearing in a complete finite
run sequence. -/
theorem topCertificateOfMembership
    {q k : Nat → α} {Tq Tk : Nat} {runs : List (Run k Tk)} {r : Run k Tk}
    (Q : Run q Tq) (hK : RunSeq k Tk 0 runs) (hr : r ∈ runs) :
    ∃ rs, ∃ hseq : RunSeq k Tk (r.hi + 1) rs,
      Nonempty (EdgeRspCertificate (fun z => lcpLen q k Tq Tk (Q.hi - z) r.lo)) := by
  obtain ⟨rs, hseq⟩ := RunSeq.exists_suffix_of_mem hK hr
  exact ⟨rs, hseq, ⟨topCertificateOfRun Q r rs hseq⟩⟩

/-- String-level top-edge closure: every K-run in the canonical finite
decomposition admits a top-edge certificate against any fixed Q-run. -/
theorem topCertificateOfStringRun
    {q k : Nat → α} {Tq Tk : Nat} (Q : Run q Tq) (r : Run k Tk)
    (hr : r ∈ fullRunList k Tk) :
    ∃ rs, ∃ hseq : RunSeq k Tk (r.hi + 1) rs,
      Nonempty (EdgeRspCertificate (fun z => lcpLen q k Tq Tk (Q.hi - z) r.lo)) :=
  topCertificateOfMembership Q (fullRunList_sound k Tk) hr

/-! ### Direct four-edge assembly from a finite boundary window -/

/-- The six consecutive runs around one mismatch rectangle, together with the
complete suffixes after `nextQ` and `nextK`.

Unlike `BoundaryRunsComplete`, this structure does not demand that a singleton
`nextQ`/`nextK` be non-singleton.  The suffix proofs let the right/top scanners
handle that case by end, mismatch, or the recursive singleton step. -/
structure BoundaryWindow (q k : Nat → α) (Tq Tk : Nat) where
  prevQ : Run q Tq
  curQ : Run q Tq
  nextQ : Run q Tq
  prevK : Run k Tk
  curK : Run k Tk
  nextK : Run k Tk
  prevQ_adj : prevQ.hi + 1 = curQ.lo
  nextQ_adj : curQ.hi + 1 = nextQ.lo
  prevK_adj : prevK.hi + 1 = curK.lo
  nextK_adj : curK.hi + 1 = nextK.lo
  qRest : List (Run q Tq)
  qRest_sound : RunSeq q Tq (nextQ.hi + 1) qRest
  kRest : List (Run k Tk)
  kRest_sound : RunSeq k Tk (nextK.hi + 1) kRest
  mismatch : curQ.sym ≠ curK.sym

namespace BoundaryWindow

variable {q k : Nat → α} {Tq Tk : Nat}

/-- Assemble the four real edge certificates.  Left/bottom use the zero or
same-symbol adapters; right/top use the finite suffix scanners. -/
def certificate (W : BoundaryWindow q k Tq Tk) :
    BoundaryRspCertificate
      (fun z => lcsLen q k W.prevQ.hi (W.curK.lo + z - 1))
      (fun z => lcsLen q k (W.curQ.lo + z - 1) W.prevK.hi)
      (fun z => lcpLen q k Tq Tk W.nextQ.lo (W.curK.hi - z))
      (fun z => lcpLen q k Tq Tk (W.curQ.hi - z) W.nextK.lo) :=
  BoundaryCertificates.four_edge_certificate
    (leftCertificateOrZero W.prevQ.maximal W.curK.maximal
      W.prevQ.nonempty W.curK.nonempty)
    (bottomCertificateOrZero W.curQ.maximal W.prevK.maximal
      W.curQ.nonempty W.prevK.nonempty)
    (rightCertificateOfRun W.curK W.nextQ W.qRest W.qRest_sound)
    (topCertificateOfRun W.curQ W.nextK W.kRest W.kRest_sound)

/-- The direct finite-window certificate retains the seven-range bound. -/
theorem certificate_range_count_le_seven (W : BoundaryWindow q k Tq Tk)
    (thrLeft thrBottom thrRight thrTop : Nat)
    (windowLo windowHi runLo runHi : Nat) :
    rangeCount
      (BoundaryRangePlan.effectiveCuts
        { records := W.certificate.toRecords
              thrLeft thrBottom thrRight thrTop
          windowLo := windowLo
          windowHi := windowHi
          runLo := runLo
          runHi := runHi }) ≤ 7 :=
  BoundaryRangeCount.boundary_rsp_certificate_range_count_le_seven
    W.certificate thrLeft thrBottom thrRight thrTop
    windowLo windowHi runLo runHi

end BoundaryWindow

/-! ### Recursive singleton scan and strict progress -/

/-- Outcome of scanning a finite suffix for the right edge.  The `step`
constructor stores the recursive scan of the strictly advanced run. -/
inductive RightOutcome {q k : Nat → α} {Tq Tk : Nat}
    (K : Run k Tk) : Run q Tq → Prop
  | base (r : Run q Tq)
      (hbase : r.sym = K.sym ∨ r.lo < r.hi ∨ K.lo = K.hi) :
      RightOutcome K r
  | singletonEnd (r : Run q Tq)
      (hsingle : r.lo = r.hi) (hend : r.hi + 1 = Tq) :
      RightOutcome K r
  | nextMismatch (r r' : Run q Tq)
      (hsingle : r.lo = r.hi) (hlo : r'.lo = r.hi + 1)
      (hne : r'.sym ≠ K.sym) :
      RightOutcome K r
  | step (r r' : Run q Tq)
      (hsingle : r.lo = r.hi) (hlo : r'.lo = r.hi + 1)
      (hnext : r'.sym = K.sym) (tail : RightOutcome K r') :
      RightOutcome K r

/-- Structural scanner over the complete suffix after `r`. -/
 theorem rightScanOutcome
    {q k : Nat → α} {Tq Tk : Nat} (K : Run k Tk) (r : Run q Tq)
    (rs : List (Run q Tq)) (hseq : RunSeq q Tq (r.hi + 1) rs) :
    RightOutcome K r := by
  by_cases hbase : r.sym = K.sym ∨ r.lo < r.hi ∨ K.lo = K.hi
  · exact RightOutcome.base r hbase
  · have hnon : ¬ r.lo < r.hi := by
      intro h
      exact hbase (Or.inr (Or.inl h))
    have hks : ¬ K.lo = K.hi := by
      intro h
      exact hbase (Or.inr (Or.inr h))
    have hsingle : r.lo = r.hi :=
      Nat.le_antisymm r.nonempty (Nat.le_of_not_gt hnon)
    cases rs with
    | nil =>
        have hend : r.hi + 1 = Tq := by
          cases hseq with
          | nil h => exact h
        exact RightOutcome.singletonEnd r hsingle hend
    | cons r' rs' =>
        cases hseq with
        | cons _ hlo htail =>
            by_cases hnext : r'.sym = K.sym
            · exact RightOutcome.step r r' hsingle hlo hnext
                (rightScanOutcome K r' rs' htail)
            · exact RightOutcome.nextMismatch r r' hsingle hlo hnext
termination_by rs.length
decreasing_by simp_all

/-- Every singleton step strictly advances the run-start index. -/
theorem rightOutcome_step_start_lt
    {q k : Nat → α} {Tq Tk : Nat} {K : Run k Tk}
    {r r' : Run q Tq} (hsingle : r.lo = r.hi)
    (hlo : r'.lo = r.hi + 1) :
    r.lo < r'.lo := by
  omega

/-- A singleton step lands immediately on a base run: the next run has the
opposite-run symbol, so the direct right-edge certificate applies. -/
theorem rightOutcome_step_closes
    {q k : Nat → α} {Tq Tk : Nat} {K : Run k Tk}
    {r r' : Run q Tq} (hsingle : r.lo = r.hi)
    (hlo : r'.lo = r.hi + 1) (hnext : r'.sym = K.sym) :
    RightOutcome K r' :=
  RightOutcome.base r' (Or.inl hnext)

/-! ### Top-edge recursive scan -/

/-- Outcome of scanning a finite K-run suffix for the top edge. -/
inductive TopOutcome {q k : Nat → α} {Tq Tk : Nat}
    (Q : Run q Tq) : Run k Tk → Prop
  | base (r : Run k Tk)
      (hbase : r.sym = Q.sym ∨ r.lo < r.hi ∨ Q.lo = Q.hi) :
      TopOutcome Q r
  | singletonEnd (r : Run k Tk)
      (hsingle : r.lo = r.hi) (hend : r.hi + 1 = Tk) :
      TopOutcome Q r
  | nextMismatch (r r' : Run k Tk)
      (hsingle : r.lo = r.hi) (hlo : r'.lo = r.hi + 1)
      (hne : r'.sym ≠ Q.sym) :
      TopOutcome Q r
  | step (r r' : Run k Tk)
      (hsingle : r.lo = r.hi) (hlo : r'.lo = r.hi + 1)
      (hnext : r'.sym = Q.sym) (tail : TopOutcome Q r') :
      TopOutcome Q r

/-- Structural scanner over the complete K-run suffix after `r`. -/
 theorem topScanOutcome
    {q k : Nat → α} {Tq Tk : Nat} (Q : Run q Tq) (r : Run k Tk)
    (rs : List (Run k Tk)) (hseq : RunSeq k Tk (r.hi + 1) rs) :
    TopOutcome Q r := by
  by_cases hbase : r.sym = Q.sym ∨ r.lo < r.hi ∨ Q.lo = Q.hi
  · exact TopOutcome.base r hbase
  · have hnon : ¬ r.lo < r.hi := by
      intro h
      exact hbase (Or.inr (Or.inl h))
    have hqs : ¬ Q.lo = Q.hi := by
      intro h
      exact hbase (Or.inr (Or.inr h))
    have hsingle : r.lo = r.hi :=
      Nat.le_antisymm r.nonempty (Nat.le_of_not_gt hnon)
    cases rs with
    | nil =>
        have hend : r.hi + 1 = Tk := by
          cases hseq with
          | nil h => exact h
        exact TopOutcome.singletonEnd r hsingle hend
    | cons r' rs' =>
        cases hseq with
        | cons _ hlo htail =>
            by_cases hnext : r'.sym = Q.sym
            · exact TopOutcome.step r r' hsingle hlo hnext
                (topScanOutcome Q r' rs' htail)
            · exact TopOutcome.nextMismatch r r' hsingle hlo hnext
termination_by rs.length
decreasing_by simp_all

/-- Every top singleton step strictly advances the K-run-start index. -/
theorem topOutcome_step_start_lt
    {q k : Nat → α} {Tq Tk : Nat} {Q : Run q Tq}
    {r r' : Run k Tk} (hsingle : r.lo = r.hi)
    (hlo : r'.lo = r.hi + 1) :
    r.lo < r'.lo := by
  omega

/-- A top singleton step lands immediately on a base run. -/
theorem topOutcome_step_closes
    {q k : Nat → α} {Tq Tk : Nat} {Q : Run q Tq}
    {r r' : Run k Tk} (hsingle : r.lo = r.hi)
    (hlo : r'.lo = r.hi + 1) (hnext : r'.sym = Q.sym) :
    TopOutcome Q r' :=
  TopOutcome.base r' (Or.inl hnext)

end BoundaryRunExtractor

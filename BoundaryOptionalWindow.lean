import BoundaryRunExtractor

/-!
## Boundary windows with optional previous/next runs

`BoundaryRunExtractor.BoundaryWindow` requires all six neighbouring runs
(`prevQ`, `curQ`, `nextQ`, `prevK`, `curK`, `nextK`).  The two string endpoints
are the only places where an immediate previous/next run can genuinely be
absent.

This file records that endpoint distinction explicitly:

* `prevQ?` and `prevK?` are optional previous runs.  `none` is allowed only at
  the string start, witnessed by `prevQ_first`/`prevK_first`; `some r` carries
  the exact adjacency proof.
* `qSuffix` and `kSuffix` start immediately after `curQ`/`curK` and cover the
  remaining finite string.  Their `head?` is the optional next run.  Keeping the
  complete suffix (rather than only its head) is what lets a singleton next run
  recurse into a farther run.
* `curQ` and `curK` are the mismatching runs around which the four boundary
  certificates are assembled.

The resulting `Window.certificate` has the same four edge orientations as the
older six-run interface.  Missing previous/next runs contribute constant-zero
edges; present runs use the finite right/top scanners.
-/

open Lcs RunRect Repair RspSummary
open BoundaryRangeCount BoundaryZeroCertificates BoundaryRecursive
open BoundaryRunExtractor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace BoundaryOptionalWindow

variable {α : Type} [DecidableEq α]

/-- A focused run inside a finite run sequence.  `prev?` is the immediate
predecessor, and `suffix` covers every run strictly after `cur` through the
string end. -/
structure RunFocus (s : Nat → α) (T lo : Nat) (cur : Run s T) where
  prev? : Option (Run s T)
  suffix : List (Run s T)
  prev_adj : ∀ p, prev? = some p → p.hi + 1 = cur.lo
  prev_missing : prev? = none → cur.lo = lo
  suffix_sound : RunSeq s T (cur.hi + 1) suffix

/-- Every run in a finite adjacent cover-complete sequence can be focused as an
optional-predecessor plus complete-suffix window. -/
theorem RunSeq.focus_of_mem
    {s : Nat → α} {T lo : Nat} {runs : List (Run s T)}
    (h : RunSeq s T lo runs) {cur : Run s T} (hmem : cur ∈ runs) :
    Nonempty (RunFocus s T lo cur) := by
  revert cur
  induction h with
  | nil =>
      intro cur hmem
      simp at hmem
  | cons r0 hlo htail ih =>
      intro cur hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hcur | hmem
      · subst hcur
        exact ⟨
          { prev? := none
            suffix := _
            prev_adj := by
              intro p hp
              cases hp
            prev_missing := by
              intro _
              exact hlo
            suffix_sound := htail }⟩
      · obtain ⟨F⟩ := ih hmem
        cases hprev : F.prev? with
        | none =>
            exact ⟨
              { prev? := some r0
                suffix := F.suffix
                prev_adj := by
                  intro p hp
                  cases hp
                  exact (F.prev_missing hprev).symm
                prev_missing := by
                  intro hp
                  cases hp
                suffix_sound := F.suffix_sound }⟩
        | some p =>
            exact ⟨
              { prev? := some p
                suffix := F.suffix
                prev_adj := by
                  intro p' hp'
                  cases hp'
                  exact F.prev_adj p hprev
                prev_missing := by
                  intro hp
                  cases hp
                suffix_sound := F.suffix_sound }⟩

/-- A boundary window whose immediate previous runs are optional and whose
immediate next runs are read as the heads of complete suffixes.

The fields `prevQ_first`/`prevK_first` say that `none` really means "at the
string start", not "the window was truncated before the predecessor".  The
suffix soundness fields say that `qSuffix`/`kSuffix` cover every run after the
current run through the corresponding string endpoint. -/
structure Window (q k : Nat → α) (Tq Tk : Nat) where
  prevQ? : Option (Run q Tq)
  curQ : Run q Tq
  prevK? : Option (Run k Tk)
  curK : Run k Tk
  qSuffix : List (Run q Tq)
  kSuffix : List (Run k Tk)
  prevQ_adj : ∀ p, prevQ? = some p → p.hi + 1 = curQ.lo
  prevQ_first : prevQ? = none → curQ.lo = 0
  prevK_adj : ∀ p, prevK? = some p → p.hi + 1 = curK.lo
  prevK_first : prevK? = none → curK.lo = 0
  qSuffix_sound : RunSeq q Tq (curQ.hi + 1) qSuffix
  kSuffix_sound : RunSeq k Tk (curK.hi + 1) kSuffix
  mismatch : curQ.sym ≠ curK.sym

namespace Window

variable {q k : Nat → α} {Tq Tk : Nat}

/-- Optional next Q run, obtained as the head of the complete Q suffix. -/
def nextQ? (W : Window q k Tq Tk) : Option (Run q Tq) :=
  match W.qSuffix with
  | [] => none
  | r :: _ => some r

/-- Optional next K run, obtained as the head of the complete K suffix. -/
def nextK? (W : Window q k Tq Tk) : Option (Run k Tk) :=
  match W.kSuffix with
  | [] => none
  | r :: _ => some r

/-- Left-edge function.  A missing previous Q run gives the constant-zero edge;
an existing previous Q run uses its right endpoint exactly as in
`BoundaryWindow`. -/
def leftFunction (W : Window q k Tq Tk) (z : Nat) : Nat :=
  match W.prevQ? with
  | none => 0
  | some p => lcsLen q k p.hi (W.curK.lo + z - 1)

/-- Bottom-edge function.  A missing previous K run gives the constant-zero
edge; an existing previous K run uses its right endpoint. -/
def bottomFunction (W : Window q k Tq Tk) (z : Nat) : Nat :=
  match W.prevK? with
  | none => 0
  | some p => lcsLen q k (W.curQ.lo + z - 1) p.hi

/-- Right-edge function.  A missing next Q run gives the constant-zero edge;
an existing next Q run uses its left endpoint. -/
def rightFunction (W : Window q k Tq Tk) (z : Nat) : Nat :=
  match W.qSuffix with
  | [] => 0
  | next :: _ => lcpLen q k Tq Tk next.lo (W.curK.hi - z)

/-- Top-edge function.  A missing next K run gives the constant-zero edge; an
existing next K run uses its left endpoint. -/
def topFunction (W : Window q k Tq Tk) (z : Nat) : Nat :=
  match W.kSuffix with
  | [] => 0
  | next :: _ => lcpLen q k Tq Tk (W.curQ.hi - z) next.lo

/-- Left-edge certificate with an optional previous Q run. -/
def leftCertificate (W : Window q k Tq Tk) :
    EdgeRspCertificate W.leftFunction := by
  cases h : W.prevQ? with
  | none =>
      exact constantZeroEdgeCertificate W.leftFunction 1
        (W.curK.hi - W.curK.lo) (by
          intro z _ _
          simp [leftFunction, h])
  | some p =>
      have hcert := leftCertificateOrZero p.maximal W.curK.maximal
        p.nonempty W.curK.nonempty
      have hfun : W.leftFunction =
          (fun z => lcsLen q k p.hi (W.curK.lo + z - 1)) := by
        funext z
        simp [leftFunction, h]
      rw [hfun]
      exact hcert

/-- Bottom-edge certificate with an optional previous K run. -/
def bottomCertificate (W : Window q k Tq Tk) :
    EdgeRspCertificate W.bottomFunction := by
  cases h : W.prevK? with
  | none =>
      exact constantZeroEdgeCertificate W.bottomFunction 1
        (W.curQ.hi - W.curQ.lo + 1) (by
          intro z _ _
          simp [bottomFunction, h])
  | some p =>
      have hcert := bottomCertificateOrZero W.curQ.maximal p.maximal
        W.curQ.nonempty p.nonempty
      have hfun : W.bottomFunction =
          (fun z => lcsLen q k (W.curQ.lo + z - 1) p.hi) := by
        funext z
        simp [bottomFunction, h]
      rw [hfun]
      exact hcert

/-- Right-edge certificate from the complete Q suffix after `curQ`.

If the suffix is empty then `curQ` reaches `Tq` and the edge is constant zero.
Otherwise its head is `nextQ`; `rightCertificateOfRun` handles all symbol
cases, including a singleton `nextQ` whose farther run is the suffix tail. -/
def rightCertificate (W : Window q k Tq Tk) :
    EdgeRspCertificate W.rightFunction := by
  cases h : W.qSuffix with
  | nil =>
      exact constantZeroEdgeCertificate W.rightFunction 0
        (W.curK.hi - W.curK.lo) (by
          intro z _ _
          simp [rightFunction, h])
  | cons next rest =>
      have hs : RunSeq q Tq (next.hi + 1) rest := by
        have hs0 := W.qSuffix_sound
        rw [h] at hs0
        cases hs0 with
        | cons _ _ tail => exact tail
      have hcert := rightCertificateOfRun W.curK next rest hs
      have hfun : W.rightFunction =
          (fun z => lcpLen q k Tq Tk next.lo (W.curK.hi - z)) := by
        funext z
        simp [rightFunction, h]
      rw [hfun]
      exact hcert

/-- Top-edge certificate from the complete K suffix after `curK`.

This is the reflected counterpart of `rightCertificate`; a singleton next K run
recurses into the farther K runs supplied by `kSuffix`. -/
def topCertificate (W : Window q k Tq Tk) :
    EdgeRspCertificate W.topFunction := by
  cases h : W.kSuffix with
  | nil =>
      exact constantZeroEdgeCertificate W.topFunction 0
        (W.curQ.hi - W.curQ.lo) (by
          intro z _ _
          simp [topFunction, h])
  | cons next rest =>
      have hs : RunSeq k Tk (next.hi + 1) rest := by
        have hs0 := W.kSuffix_sound
        rw [h] at hs0
        cases hs0 with
        | cons _ _ tail => exact tail
      have hcert := topCertificateOfRun W.curQ next rest hs
      have hfun : W.topFunction =
          (fun z => lcpLen q k Tq Tk (W.curQ.hi - z) next.lo) := by
        funext z
        simp [topFunction, h]
      rw [hfun]
      exact hcert

/-- Assemble the four optional-neighbour edge certificates. -/
def certificate (W : Window q k Tq Tk) :
    BoundaryRspCertificate
      W.leftFunction W.bottomFunction W.rightFunction W.topFunction :=
  BoundaryCertificates.four_edge_certificate
    W.leftCertificate W.bottomCertificate W.rightCertificate W.topCertificate

/-- The optional-neighbour boundary compiler retains the seven-range bound. -/
theorem certificate_range_count_le_seven (W : Window q k Tq Tk)
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

/-- Exact endpoint-coverage consequences of the window fields: absent previous
runs are first runs, absent next runs are last runs, and present neighbours are
adjacent in both directions. -/
theorem coverage (W : Window q k Tq Tk) :
    (∀ p, W.prevQ? = some p → p.hi + 1 = W.curQ.lo) ∧
    (W.prevQ? = none → W.curQ.lo = 0) ∧
    (∀ p, W.prevK? = some p → p.hi + 1 = W.curK.lo) ∧
    (W.prevK? = none → W.curK.lo = 0) ∧
    (∀ p, W.nextQ? = some p → W.curQ.hi + 1 = p.lo) ∧
    (W.nextQ? = none → W.curQ.hi + 1 = Tq) ∧
    (∀ p, W.nextK? = some p → W.curK.hi + 1 = p.lo) ∧
    (W.nextK? = none → W.curK.hi + 1 = Tk) := by
  refine ⟨W.prevQ_adj, W.prevQ_first, W.prevK_adj, W.prevK_first,
    ?_, ?_, ?_, ?_⟩
  · cases h : W.qSuffix with
    | nil =>
        have hnext : W.nextQ? = none := by simp [nextQ?, h]
        intro p hp
        rw [hnext] at hp
        cases hp
    | cons next rest =>
        have hnext : W.nextQ? = some next := by simp [nextQ?, h]
        intro p hp
        have hp' : next = p := by simpa [hnext] using hp
        subst p
        have hs := W.qSuffix_sound
        rw [h] at hs
        cases hs with
        | cons _ hlo _ => exact hlo.symm
  · cases h : W.qSuffix with
    | nil =>
        intro _
        have hs := W.qSuffix_sound
        rw [h] at hs
        cases hs with
        | nil hend => exact hend
    | cons next rest =>
        have hnext : W.nextQ? = some next := by simp [nextQ?, h]
        intro hn
        rw [hnext] at hn
        cases hn
  · cases h : W.kSuffix with
    | nil =>
        have hnext : W.nextK? = none := by simp [nextK?, h]
        intro p hp
        rw [hnext] at hp
        cases hp
    | cons next rest =>
        have hnext : W.nextK? = some next := by simp [nextK?, h]
        intro p hp
        have hp' : next = p := by simpa [hnext] using hp
        subst p
        have hs := W.kSuffix_sound
        rw [h] at hs
        cases hs with
        | cons _ hlo _ => exact hlo.symm
  · cases h : W.kSuffix with
    | nil =>
        intro _
        have hs := W.kSuffix_sound
        rw [h] at hs
        cases hs with
        | nil hend => exact hend
    | cons next rest =>
        have hnext : W.nextK? = some next := by simp [nextK?, h]
        intro hn
        rw [hnext] at hn
        cases hn

/-- Any pair of mismatching runs occurring in arbitrary finite cover-complete Q
and K run sequences can be assembled into an optional-neighbour boundary
window. -/
theorem exists_window_of_runSeq_mem
    {qRuns : List (Run q Tq)} {kRuns : List (Run k Tk)}
    (hQ : RunSeq q Tq 0 qRuns) (hK : RunSeq k Tk 0 kRuns)
    {curQ : Run q Tq} {curK : Run k Tk}
    (hQmem : curQ ∈ qRuns) (hKmem : curK ∈ kRuns)
    (hmismatch : curQ.sym ≠ curK.sym) :
    ∃ W : Window q k Tq Tk, W.curQ = curQ ∧ W.curK = curK := by
  obtain ⟨Fq⟩ := RunSeq.focus_of_mem hQ hQmem
  obtain ⟨Fk⟩ := RunSeq.focus_of_mem hK hKmem
  refine ⟨
    { prevQ? := Fq.prev?
      curQ := curQ
      prevK? := Fk.prev?
      curK := curK
      qSuffix := Fq.suffix
      kSuffix := Fk.suffix
      prevQ_adj := Fq.prev_adj
      prevQ_first := Fq.prev_missing
      prevK_adj := Fk.prev_adj
      prevK_first := Fk.prev_missing
      qSuffix_sound := Fq.suffix_sound
      kSuffix_sound := Fk.suffix_sound
      mismatch := hmismatch }, rfl, rfl⟩

/-- Canonical finite-run-list form of `exists_window_of_runSeq_mem`: every
mismatching pair of runs in the strings `q[0..Tq)` and `k[0..Tk)` has an
optional-neighbour window and therefore a four-edge certificate. -/
theorem exists_window_of_fullRunList_mem
    {curQ : Run q Tq} {curK : Run k Tk}
    (hQmem : curQ ∈ fullRunList q Tq)
    (hKmem : curK ∈ fullRunList k Tk)
    (hmismatch : curQ.sym ≠ curK.sym) :
    ∃ W : Window q k Tq Tk, W.curQ = curQ ∧ W.curK = curK :=
  exists_window_of_runSeq_mem (fullRunList_sound q Tq) (fullRunList_sound k Tk)
    hQmem hKmem hmismatch

/-- The old six-run `BoundaryWindow` is the all-`some`/nonempty-suffix instance
of the optional-neighbour window. -/
def ofBoundaryWindow (W : BoundaryRunExtractor.BoundaryWindow q k Tq Tk) :
    Window q k Tq Tk where
  prevQ? := some W.prevQ
  curQ := W.curQ
  prevK? := some W.prevK
  curK := W.curK
  qSuffix := W.nextQ :: W.qRest
  kSuffix := W.nextK :: W.kRest
  prevQ_adj := by
    intro p hp
    cases hp
    exact W.prevQ_adj
  prevQ_first := by
    intro hp
    cases hp
  prevK_adj := by
    intro p hp
    cases hp
    exact W.prevK_adj
  prevK_first := by
    intro hp
    cases hp
  qSuffix_sound := RunSeq.cons W.nextQ W.nextQ_adj.symm W.qRest_sound
  kSuffix_sound := RunSeq.cons W.nextK W.nextK_adj.symm W.kRest_sound
  mismatch := W.mismatch

end Window

end BoundaryOptionalWindow

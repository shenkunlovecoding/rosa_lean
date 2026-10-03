import BoundaryZeroCertificates

/-!
## Recursive and string-end boundary cases

`BoundaryZeroCertificates` closes the same-symbol runs and the non-singleton
mismatch corners.  Two cases are still outside that interface:

* a string may begin/end before a `prev`/`next` run exists; then the relevant
  context is identically zero;
* a mismatching `next` run of length one lets an open-edge forward context cross
  that run and recurse into the following run.

This file keeps the recursion mathematical rather than unfolding a finite
number of runs.  The singleton step returns an ordinary `RspShape` whose
`gamma` is the context after the further run; the further context is an opaque
natural number and may itself be resolved by another step.  The missing-run
case is the base case.
-/

open Lcs RunRect Repair RspSummary BoundaryRangeCount BoundaryZeroCertificates

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace BoundaryRecursive

variable {α : Type} [DecidableEq α]

/-! ### Forward-context successor decomposition -/

/-- Decompose a forward prefix equality after the first symbol. -/
theorem prefixEq_succ_iff
    {q k : Nat → α} {Tq Tk p u R : Nat}
    (hpT : p + 1 < Tq) (huT : u + 1 < Tk) :
    PrefixEq q k Tq Tk p u (R + 1) ↔
      q (p + 1) = k (u + 1) ∧
        PrefixEq q k Tq Tk (p + 1) (u + 1) R := by
  constructor
  · intro h
    constructor
    · have h0 := h.2.2 0 (by simp)
      simpa using h0
    · refine ⟨?_, ?_, ?_⟩
      · have hb := h.1
        omega
      · have hb := h.2.1
        omega
      · intro h' hh'
        rw [List.mem_range] at hh'
        have hh : h' + 1 ∈ List.range (R + 1) := by
          exact List.mem_range.mpr (by omega)
        have hh'' := h.2.2 (h' + 1) hh
        have hidxq : p + 1 + 1 + h' = p + 1 + (h' + 1) := by omega
        have hidxk : u + 1 + 1 + h' = u + 1 + (h' + 1) := by omega
        simpa [hidxq, hidxk] using hh''
  · rintro ⟨hhead, htail⟩
    refine ⟨?_, ?_, ?_⟩
    · have hb := htail.1
      omega
    · have hb := htail.2.1
      omega
    · intro h' hh'
      rw [List.mem_range] at hh'
      by_cases hzero : h' = 0
      · subst hzero
        simpa using hhead
      · have hpos : 0 < h' := by omega
        have hm : h' - 1 ∈ List.range R := by
          rw [List.mem_range]
          omega
        have hh := htail.2.2 (h' - 1) hm
        have hidxq : p + 1 + 1 + (h' - 1) = p + 1 + h' := by omega
        have hidxk : u + 1 + 1 + (h' - 1) = u + 1 + h' := by omega
        rw [hidxq, hidxk] at hh
        exact hh

/-- If the first forward symbols agree, the maximal forward context is one plus
the context starting immediately after them. -/
theorem lcpLen_succ_eq_of_head_eq
    {q k : Nat → α} {Tq Tk p u : Nat}
    (hpT : p + 1 < Tq) (huT : u + 1 < Tk)
    (hhead : q (p + 1) = k (u + 1)) :
    lcpLen q k Tq Tk p u = 1 + lcpLen q k Tq Tk (p + 1) (u + 1) := by
  apply Nat.le_antisymm
  · let L := lcpLen q k Tq Tk p u
    have hone : PrefixEq q k Tq Tk p u 1 := by
      rw [show 1 = 0 + 1 by omega, prefixEq_succ_iff hpT huT]
      exact ⟨hhead, prefixEq_zero q k Tq Tk (p + 1) (u + 1)⟩
    have hLpos : 0 < L := by
      have hle : 1 ≤ L := lcpLen_greatest hone
      omega
    have htail : PrefixEq q k Tq Tk (p + 1) (u + 1) (L - 1) := by
      have hspec := lcpLen_spec q k Tq Tk p u
      have hspec' : PrefixEq q k Tq Tk p u ((L - 1) + 1) := by
        simpa [Nat.sub_add_cancel (by omega : 0 < L)] using hspec
      exact ((prefixEq_succ_iff (p := p) (u := u) (R := L - 1) hpT huT).1 hspec').2
    have hle : L - 1 ≤ lcpLen q k Tq Tk (p + 1) (u + 1) :=
      lcpLen_greatest htail
    omega
  · have htail := lcpLen_spec q k Tq Tk (p + 1) (u + 1)
    have hprefix : PrefixEq q k Tq Tk p u (1 + lcpLen q k Tq Tk (p + 1) (u + 1)) := by
      rw [show 1 + lcpLen q k Tq Tk (p + 1) (u + 1) =
          lcpLen q k Tq Tk (p + 1) (u + 1) + 1 by omega,
        prefixEq_succ_iff hpT huT]
      exact ⟨hhead, htail⟩
    exact lcpLen_greatest hprefix

/-- If the first forward symbols disagree, the forward context is zero. -/
theorem lcpLen_zero_of_head_ne
    {q k : Nat → α} {Tq Tk p u : Nat}
    (hne : q (p + 1) ≠ k (u + 1)) :
    lcpLen q k Tq Tk p u = 0 := by
  apply RunRectLcp.lcpLen_eq_of (prefixEq_zero q k Tq Tk p u)
  intro hcon
  have h0 := hcon.2.2 0 (by simp)
  exact hne (by simpa using h0)

/-! ### String-start and string-end base cases -/

/-- Missing previous Q run: the left context is zero on the non-corner left-edge
window `z = 1..|curK|-1`. -/
def leftMissingPrevCertificate
    {q k : Nat → α} {Tq Tk a c d : Nat}
    (ha : a = 0) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => leftCtx q k a (c + z)) :=
  constantZeroEdgeCertificate (fun z => leftCtx q k a (c + z)) 1 (d - c)
    (by
      intro z _hz1 _hz2
      simp [leftCtx, ha])

/-- Missing previous K run: the bottom context is zero along the bottom edge. -/
def bottomMissingPrevCertificate
    {q k : Nat → α} {Tq Tk a b c : Nat}
    (hc : c = 0) (hab : a ≤ b) :
    EdgeRspCertificate (fun z => leftCtx q k (a + z) c) :=
  constantZeroEdgeCertificate (fun z => leftCtx q k (a + z) c) 0 (b - a)
    (by
      intro _z _hz0 _hz
      simp [leftCtx, hc])

/-- Missing next Q run: the forward context after the Q string end is zero. -/
def rightMissingNextCertificate
    {q k : Nat → α} {Tq Tk a c d : Nat}
    (ha : a = Tq) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk a (d - z)) :=
  constantZeroEdgeCertificate (fun z => lcpLen q k Tq Tk a (d - z)) 0 (d - c)
    (by
      intro z _hz0 _hz
      have hle := RunRectLcp.lcpLen_le_bound q k Tq Tk a (d - z)
      have hz : Tq - a - 1 = 0 := by omega
      have hmin : min (Tq - a - 1) (Tk - (d - z) - 1) = 0 := by
        simp [hz]
      omega)

/-- Missing next K run: the forward context after the K string end is zero. -/
def topMissingNextCertificate
    {q k : Nat → α} {Tq Tk a b c : Nat}
    (hc : c = Tk) (hab : a ≤ b) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (b - z) c) :=
  constantZeroEdgeCertificate (fun z => lcpLen q k Tq Tk (b - z) c) 0 (b - a)
    (by
      intro z _hz0 _hz
      have hle := RunRectLcp.lcpLen_le_bound q k Tq Tk (b - z) c
      have hz : Tk - c - 1 = 0 := by omega
      have hmin : min (Tq - (b - z) - 1) (Tk - c - 1) = 0 := by
        simp [hz]
      omega)

/-! ### Singleton next-run steps -/

/-- Right-edge recursive step.  The singleton next Q run is `[a,a]`; the
following Q run is `[a+1,b]` and its symbol equals the current K symbol.  The
open-edge context is an RSP whose spike is the length of the following Q run and
whose `gamma` is the still-abstract context after that run. -/
theorem right_singleton_rsp
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hSingleton : ConstRun q Tq a a αs)
    (hNext : ConstRun q Tq (a + 1) b βs)
    (hNext_nonempty : a + 1 ≤ b)
    (hK : ConstRun k Tk c d βs)
    (hK_nonempty : c ≤ d) :
    RspShape (fun z => lcpLen q k Tq Tk a (d - z))
      (b - a) (lcpLen q k Tq Tk b d) 1 (d - c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz1 hzlt hzn
    have hpT : a + 1 < Tq := by have := hNext.hi_lt; omega
    have huT : d - z + 1 < Tk := by have := hK.hi_lt; omega
    have huc : c ≤ d - z + 1 := by omega
    have hud : d - z + 1 ≤ d := by omega
    have hhead : q (a + 1) = k (d - z + 1) := by
      rw [hNext.mem (a + 1) (by omega) (by omega),
        hK.mem (d - z + 1) huc hud]
    have hsucc := lcpLen_succ_eq_of_head_eq
      (q := q) (k := k) (Tq := Tq) (Tk := Tk) (p := a) (u := d - z)
      hpT huT hhead
    have hstd := RunRectLcp.repair_edge_right_rsp
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a + 1) (b := b) (c := c) (d := d)
      (αs := βs) (βs := βs) hNext hK rfl
      (p := a + 1) (u := d - z + 1) (by omega) (by omega) huc hud
    have hcond1 : ¬ b - (a + 1) < d - (d - z + 1) := by omega
    have hcond2 : ¬ b - (a + 1) = d - (d - z + 1) := by omega
    rw [if_neg hcond1, if_neg hcond2] at hstd
    rw [hsucc, hstd]
    omega
  · intro z hz1 hzeq hzn
    subst z
    have hpT : a + 1 < Tq := by have := hNext.hi_lt; omega
    have huT : d - (b - a) + 1 < Tk := by have := hK.hi_lt; omega
    have huc : c ≤ d - (b - a) + 1 := by omega
    have hud : d - (b - a) + 1 ≤ d := by omega
    have hhead : q (a + 1) = k (d - (b - a) + 1) := by
      rw [hNext.mem (a + 1) (by omega) (by omega),
        hK.mem (d - (b - a) + 1) huc hud]
    have hsucc := lcpLen_succ_eq_of_head_eq
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (p := a) (u := d - (b - a)) hpT huT hhead
    have hstd := RunRectLcp.repair_edge_right_rsp
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a + 1) (b := b) (c := c) (d := d)
      (αs := βs) (βs := βs) hNext hK rfl
      (p := a + 1) (u := d - (b - a) + 1)
      (by omega) (by omega) huc hud
    have hcond1 : ¬ b - (a + 1) < d - (d - (b - a) + 1) := by omega
    have hcond2 : b - (a + 1) = d - (d - (b - a) + 1) := by omega
    rw [if_neg hcond1, if_pos hcond2] at hstd
    rw [hsucc, hstd]
    omega
  · intro z hz1 hzgt hzn
    have hpT : a + 1 < Tq := by have := hNext.hi_lt; omega
    have huT : d - z + 1 < Tk := by have := hK.hi_lt; omega
    have huc : c ≤ d - z + 1 := by omega
    have hud : d - z + 1 ≤ d := by omega
    have hhead : q (a + 1) = k (d - z + 1) := by
      rw [hNext.mem (a + 1) (by omega) (by omega),
        hK.mem (d - z + 1) huc hud]
    have hsucc := lcpLen_succ_eq_of_head_eq
      (q := q) (k := k) (Tq := Tq) (Tk := Tk) (p := a) (u := d - z)
      hpT huT hhead
    have hstd := RunRectLcp.repair_edge_right_rsp
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a + 1) (b := b) (c := c) (d := d)
      (αs := βs) (βs := βs) hNext hK rfl
      (p := a + 1) (u := d - z + 1) (by omega) (by omega) huc hud
    have hcond1 : b - (a + 1) < d - (d - z + 1) := by omega
    rw [if_pos hcond1] at hstd
    rw [hsucc, hstd]
    omega

/-- Top-edge recursive step, symmetric to `right_singleton_rsp`.  The singleton
next K run is `[c,c]`; the following K run is `[c+1,d]` and its symbol equals the
current Q symbol. -/
theorem top_singleton_rsp
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs)
    (hQ_nonempty : a ≤ b)
    (hSingleton : ConstRun k Tk c c βs)
    (hNext : ConstRun k Tk (c + 1) d αs)
    (hNext_nonempty : c + 1 ≤ d) :
    RspShape (fun z => lcpLen q k Tq Tk (b - z) c)
      (d - c) (lcpLen q k Tq Tk b d) 1 (b - a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz1 hzlt hzn
    have hpT : b - z + 1 < Tq := by have := hQ.hi_lt; omega
    have huT : c + 1 < Tk := by have := hNext.hi_lt; omega
    have hqlo : a ≤ b - z + 1 := by omega
    have hqhi : b - z + 1 ≤ b := by omega
    have hhead : q (b - z + 1) = k (c + 1) := by
      rw [hQ.mem (b - z + 1) hqlo hqhi,
        hNext.mem (c + 1) (by omega) (by omega)]
    have hsucc := lcpLen_succ_eq_of_head_eq
      (q := q) (k := k) (Tq := Tq) (Tk := Tk) (p := b - z) (u := c)
      hpT huT hhead
    have hstd := RunRectLcp.repair_edge_right_rsp
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c + 1) (d := d)
      (αs := αs) (βs := αs) hQ hNext rfl
      (p := b - z + 1) (u := c + 1)
      hqlo (by omega) (by omega) (by omega)
    have hx : b - (b - z + 1) = z - 1 := by omega
    have hy : d - (c + 1) = d - c - 1 := by omega
    have hcond1 : b - (b - z + 1) < d - (c + 1) := by
      rw [hx, hy]
      omega
    rw [if_pos hcond1] at hstd
    rw [hsucc, hstd]
    omega
  · intro z hz1 hzeq hzn
    subst z
    have hpT : b - (d - c) + 1 < Tq := by have := hQ.hi_lt; omega
    have huT : c + 1 < Tk := by have := hNext.hi_lt; omega
    have hqlo : a ≤ b - (d - c) + 1 := by omega
    have hqhi : b - (d - c) + 1 ≤ b := by omega
    have hhead : q (b - (d - c) + 1) = k (c + 1) := by
      rw [hQ.mem (b - (d - c) + 1) hqlo hqhi,
        hNext.mem (c + 1) (by omega) (by omega)]
    have hsucc := lcpLen_succ_eq_of_head_eq
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (p := b - (d - c)) (u := c) hpT huT hhead
    have hstd := RunRectLcp.repair_edge_right_rsp
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c + 1) (d := d)
      (αs := αs) (βs := αs) hQ hNext rfl
      (p := b - (d - c) + 1) (u := c + 1)
      hqlo (by omega) (by omega) (by omega)
    have hcond1 : ¬ b - (b - (d - c) + 1) < d - (c + 1) := by omega
    have hcond2 : b - (b - (d - c) + 1) = d - (c + 1) := by omega
    rw [if_neg hcond1, if_pos hcond2] at hstd
    rw [hsucc, hstd]
    omega
  · intro z hz1 hzgt hzn
    have hpT : b - z + 1 < Tq := by have := hQ.hi_lt; omega
    have huT : c + 1 < Tk := by have := hNext.hi_lt; omega
    have hqlo : a ≤ b - z + 1 := by omega
    have hqhi : b - z + 1 ≤ b := by omega
    have hhead : q (b - z + 1) = k (c + 1) := by
      rw [hQ.mem (b - z + 1) hqlo hqhi,
        hNext.mem (c + 1) (by omega) (by omega)]
    have hsucc := lcpLen_succ_eq_of_head_eq
      (q := q) (k := k) (Tq := Tq) (Tk := Tk) (p := b - z) (u := c)
      hpT huT hhead
    have hstd := RunRectLcp.repair_edge_right_rsp
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c + 1) (d := d)
      (αs := αs) (βs := αs) hQ hNext rfl
      (p := b - z + 1) (u := c + 1)
      hqlo (by omega) (by omega) (by omega)
    have hx : b - (b - z + 1) = z - 1 := by omega
    have hy : d - (c + 1) = d - c - 1 := by omega
    have hcond1 : ¬ b - (b - z + 1) < d - (c + 1) := by
      rw [hx, hy]
      omega
    have hcond2 : ¬ b - (b - z + 1) = d - (c + 1) := by
      rw [hx, hy]
      omega
    rw [if_neg hcond1, if_neg hcond2] at hstd
    rw [hsucc, hstd]
    omega

/-- Singleton next Q run at the string end: the open right-edge context is zero. -/
def rightSingletonEndCertificate
    {q k : Nat → α} {Tq Tk a c d : Nat} {αs βs : α}
    (hSingleton : ConstRun q Tq a a αs) (hend : a + 1 = Tq)
    (hK : ConstRun k Tk c d βs) (hK_nonempty : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk a (d - z)) :=
  constantZeroEdgeCertificate (fun z => lcpLen q k Tq Tk a (d - z)) 1 (d - c)
    (by
      intro z _hz1 _hz
      have hle := RunRectLcp.lcpLen_le_bound q k Tq Tk a (d - z)
      have hz : Tq - a - 1 = 0 := by omega
      have hmin : min (Tq - a - 1) (Tk - (d - z) - 1) = 0 := by
        simp [hz]
      omega)

/-- Singleton next K run at the string end: the open top-edge context is zero. -/
def topSingletonEndCertificate
    {q k : Nat → α} {Tq Tk a b c : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hQ_nonempty : a ≤ b)
    (hSingleton : ConstRun k Tk c c βs) (hend : c + 1 = Tk) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (b - z) c) :=
  constantZeroEdgeCertificate (fun z => lcpLen q k Tq Tk (b - z) c) 1 (b - a)
    (by
      intro z _hz1 _hz
      have hle := RunRectLcp.lcpLen_le_bound q k Tq Tk (b - z) c
      have hz : Tk - c - 1 = 0 := by omega
      have hmin : min (Tq - (b - z) - 1) (Tk - c - 1) = 0 := by
        simp [hz]
      omega)

/-- Singleton next Q followed by a different-symbol Q run: the open right-edge
context is zero before the later run can be reached. -/
def rightSingletonMismatchZeroCertificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs γ βs : α}
    (hSingleton : ConstRun q Tq a a αs)
    (hNext : ConstRun q Tq (a + 1) b γ) (hNext_nonempty : a + 1 ≤ b)
    (hK : ConstRun k Tk c d βs) (hK_nonempty : c ≤ d) (hne : γ ≠ βs) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk a (d - z)) :=
  constantZeroEdgeCertificate (fun z => lcpLen q k Tq Tk a (d - z)) 1 (d - c)
    (by
      intro z hz1 hzn
      have huc : c ≤ d - z + 1 := by omega
      have hud : d - z + 1 ≤ d := by omega
      apply lcpLen_zero_of_head_ne
      rw [hNext.mem (a + 1) (by omega) (by omega),
        hK.mem (d - z + 1) huc hud]
      exact hne)

/-- Singleton next K followed by a different-symbol K run: the open top-edge
context is zero before the later run can be reached. -/
def topSingletonMismatchZeroCertificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs γ βs : α}
    (hQ : ConstRun q Tq a b αs) (hQ_nonempty : a ≤ b)
    (hSingleton : ConstRun k Tk c c βs)
    (hNext : ConstRun k Tk (c + 1) d γ) (hNext_nonempty : c + 1 ≤ d)
    (hne : γ ≠ αs) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (b - z) c) :=
  constantZeroEdgeCertificate (fun z => lcpLen q k Tq Tk (b - z) c) 1 (b - a)
    (by
      intro z hz1 hzn
      have hqlo : a ≤ b - z + 1 := by omega
      have hqhi : b - z + 1 ≤ b := by omega
      apply lcpLen_zero_of_head_ne
      rw [hQ.mem (b - z + 1) hqlo hqhi,
        hNext.mem (c + 1) (by omega) (by omega)]
      exact fun h => hne h.symm)

/-- Package the singleton step as an edge certificate. -/
def rightSingletonRecursiveCertificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hSingleton : ConstRun q Tq a a αs)
    (hNext : ConstRun q Tq (a + 1) b βs)
    (hNext_nonempty : a + 1 ≤ b)
    (hK : ConstRun k Tk c d βs)
    (hK_nonempty : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk a (d - z)) where
  lo := 1
  spike := b - a
  hi := d - c
  gamma := lcpLen q k Tq Tk b d
  shape := right_singleton_rsp hSingleton hNext hNext_nonempty hK hK_nonempty

/-- Package the top singleton step as an edge certificate. -/
def topSingletonRecursiveCertificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs)
    (hQ_nonempty : a ≤ b)
    (hSingleton : ConstRun k Tk c c βs)
    (hNext : ConstRun k Tk (c + 1) d αs)
    (hNext_nonempty : c + 1 ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (b - z) c) where
  lo := 1
  spike := d - c
  hi := b - a
  gamma := lcpLen q k Tq Tk b d
  shape := top_singleton_rsp hQ hQ_nonempty hSingleton hNext hNext_nonempty

/-! ### Direct four-edge assembly -/

/-- Assemble four arbitrary edge certificates.  This is the interface used when
some neighboring runs are absent or when a singleton step carries an abstract
further-run `gamma`. -/
def assembleCertificate
    {fLeft fBottom fRight fTop : Nat → Nat}
    (left : EdgeRspCertificate fLeft)
    (bottom : EdgeRspCertificate fBottom)
    (right : EdgeRspCertificate fRight)
    (top : EdgeRspCertificate fTop) :
    BoundaryRspCertificate fLeft fBottom fRight fTop :=
  BoundaryCertificates.four_edge_certificate left bottom right top

/-- The assembled direct interface retains the seven-range bound. -/
theorem assembleCertificate_range_count_le_seven
    {fLeft fBottom fRight fTop : Nat → Nat}
    (left : EdgeRspCertificate fLeft)
    (bottom : EdgeRspCertificate fBottom)
    (right : EdgeRspCertificate fRight)
    (top : EdgeRspCertificate fTop)
    (thrLeft thrBottom thrRight thrTop : Nat)
    (windowLo windowHi runLo runHi : Nat) :
    rangeCount
      (BoundaryRangePlan.effectiveCuts
        { records :=
            (assembleCertificate left bottom right top).toRecords
              thrLeft thrBottom thrRight thrTop
          windowLo := windowLo
          windowHi := windowHi
          runLo := runLo
          runHi := runHi }) ≤ 7 :=
  BoundaryCertificates.four_edge_boundary_rsp_certificate_range_count_le_seven
    left bottom right top thrLeft thrBottom thrRight thrTop
    windowLo windowHi runLo runHi

/-- The existing six-run assembly is an instance of the direct interface. -/
def completeToDirect
    {q k : Nat → α} {Tq Tk : Nat}
    (r : BoundaryZeroCertificates.BoundaryRunsComplete q k Tq Tk) :
    BoundaryRspCertificate
      (fun z => lcsLen q k r.prevQHi (r.curKLo + z - 1))
      (fun z => lcsLen q k (r.curQLo + z - 1) r.prevKHi)
      (fun z => lcpLen q k Tq Tk r.nextQLo (r.curKHi - z))
      (fun z => lcpLen q k Tq Tk (r.curQHi - z) r.nextKLo) :=
  r.certificate

/-- The existing complete-run range bound through the direct assembly name. -/
theorem completeToDirect_range_count_le_seven
    {q k : Nat → α} {Tq Tk : Nat}
    (r : BoundaryZeroCertificates.BoundaryRunsComplete q k Tq Tk)
    (thrLeft thrBottom thrRight thrTop : Nat)
    (windowLo windowHi runLo runHi : Nat) :
    rangeCount
      (BoundaryRangePlan.effectiveCuts
        { records :=
            (completeToDirect r).toRecords thrLeft thrBottom thrRight thrTop
          windowLo := windowLo
          windowHi := windowHi
          runLo := runLo
          runHi := runHi }) ≤ 7 :=
  r.certificate_range_count_le_seven
    thrLeft thrBottom thrRight thrTop windowLo windowHi runLo runHi

end BoundaryRecursive

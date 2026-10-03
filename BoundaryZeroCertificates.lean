import BoundaryCertificates

/-!
## Zero branches for the four repair-boundary edges

`BoundaryCertificates` assembles the four RSP certificates only for same-symbol
adjacent runs.  This file supplies the missing symbol-mismatch branches.

Two facts must be kept apart:

* on the open part of an edge, a symbol mismatch gives the constant-zero RSP;
* at the corner where the next run starts, a right/top context may continue
  through that next run, so its exact mismatch shape is a zero spike at offset
  zero rather than a constant-zero shape on the closed edge.

The file also gives guarded adaptations of the existing left/right
certificates.  Their recursive parameters are `Repair.leftCtx` and
`Repair.rightCtx`, so no positivity of the raw underflowing index is assumed.
-/

open Lcs RunRect Repair RspSummary

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace BoundaryZeroCertificates

open BoundaryRangeCount

variable {α : Type} [DecidableEq α]

/-! ### Generic zero and corner-spike RSP certificates -/

/-- A constant-zero RSP on the natural window `[lo,hi]` (possibly empty). -/
def constantZeroEdgeCertificate (f : Nat → Nat) (lo hi : Nat)
    (hzero : ∀ z, lo ≤ z → z ≤ hi → f z = 0) :
    EdgeRspCertificate f where
  lo := lo
  spike := 0
  hi := hi
  gamma := 0
  shape := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hl hz hzn
      omega
    · intro z hl hz hzn
      subst z
      simpa using hzero 0 hl hzn
    · intro z hl hz hzn
      exact hzero z hl hzn

/-- The exact mismatch shape on a right/top edge: zero at every positive offset
and a possible corner spike at offset zero. -/
def cornerSpikeEdgeCertificate (f : Nat → Nat) (hi gamma : Nat)
    (hzeroCorner : f 0 = gamma)
    (hzeroOpen : ∀ z, 1 ≤ z → z ≤ hi → f z = 0) :
    EdgeRspCertificate f where
  lo := 0
  spike := 0
  hi := hi
  gamma := gamma
  shape := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hl hz hzn
      omega
    · intro z hl hz hzn
      subst z
      simpa using hzeroCorner
    · intro z hl hz hzn
      exact hzeroOpen z (by omega) hzn

/-! ### Exact zero facts on the open edges -/

theorem left_mismatch_zero
    {q k : Nat → α} {Tq Tk ap bp c d : Nat} {αs βs : α}
    (hQp : ConstRun q Tq ap bp αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hab : ap ≤ bp) (hcd : c ≤ d) :
    ∀ z, 1 ≤ z → z ≤ d - c →
      lcsLen q k bp (c + z - 1) = 0 := by
  intro z hz1 hz
  exact RunRect.run_rectangle_symbol_ne (q := q) (k := k)
    (Tq := Tq) (Tk := Tk) (a := ap) (b := bp) (c := c) (d := d)
    (αs := αs) (βs := βs) hQp hK hne
    (t := bp) (e := c + z - 1)
    hab (Nat.le_refl bp) (by omega) (by omega)

theorem bottom_mismatch_zero
    {q k : Nat → α} {Tq Tk a b cp dp : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hKprev : ConstRun k Tk cp dp βs)
    (hne : αs ≠ βs) (hab : a ≤ b) (hcpd : cp ≤ dp) :
    ∀ z, 1 ≤ z → z ≤ b - a + 1 →
      lcsLen q k (a + z - 1) dp = 0 := by
  intro z hz1 hz
  exact RunRect.run_rectangle_symbol_ne (q := q) (k := k)
    (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := cp) (d := dp)
    (αs := αs) (βs := βs) hQ hKprev hne
    (t := a + z - 1) (e := dp)
    (by omega) (by omega) hcpd (Nat.le_refl dp)

theorem right_mismatch_zero_of_open
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hopen : c < d → a < b) (hcd : c ≤ d) :
    ∀ z, 1 ≤ z → z ≤ d - c →
      lcpLen q k Tq Tk a (d - z) = 0 := by
  intro z hz1 hz
  have hcdlt : c < d := by omega
  have hab : a < b := hopen hcdlt
  exact RunRectLcp.lcp_rectangle_symbol_ne (q := q) (k := k)
    (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := c) (d := d)
    (αs := αs) (βs := βs) hQ hK hne
    (p := a) (u := d - z)
    (Nat.le_refl a) hab (by omega) (by omega)

theorem top_mismatch_zero_of_open
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hopen : a < b → c < d) (hab : a ≤ b) :
    ∀ z, 1 ≤ z → z ≤ b - a →
      lcpLen q k Tq Tk (b - z) c = 0 := by
  intro z hz1 hz
  have hablt : a < b := by omega
  have hcdlt : c < d := hopen hablt
  exact RunRectLcp.lcp_rectangle_symbol_ne (q := q) (k := k)
    (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := c) (d := d)
    (αs := αs) (βs := βs) hQ hK hne
    (p := b - z) (u := c)
    (by omega) (by omega) (Nat.le_refl c) hcdlt

/-! ### Constant-zero certificates for the four open edges -/

def leftZeroCertificate
    {q k : Nat → α} {Tq Tk ap bp c d : Nat} {αs βs : α}
    (hQp : ConstRun q Tq ap bp αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hab : ap ≤ bp) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcsLen q k bp (c + z - 1)) :=
  constantZeroEdgeCertificate
    (fun z => lcsLen q k bp (c + z - 1)) 1 (d - c)
    (left_mismatch_zero hQp hK hne hab hcd)

def bottomZeroCertificate
    {q k : Nat → α} {Tq Tk a b cp dp : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hKprev : ConstRun k Tk cp dp βs)
    (hne : αs ≠ βs) (hab : a ≤ b) (hcpd : cp ≤ dp) :
    EdgeRspCertificate (fun z => lcsLen q k (a + z - 1) dp) :=
  constantZeroEdgeCertificate
    (fun z => lcsLen q k (a + z - 1) dp) 1 (b - a + 1)
    (bottom_mismatch_zero hQ hKprev hne hab hcpd)

def rightZeroOpenCertificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hopen : c < d → a < b) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk a (d - z)) :=
  constantZeroEdgeCertificate
    (fun z => lcpLen q k Tq Tk a (d - z)) 1 (d - c)
    (right_mismatch_zero_of_open hQ hK hne hopen hcd)

def topZeroOpenCertificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hopen : a < b → c < d) (hab : a ≤ b) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (b - z) c) :=
  constantZeroEdgeCertificate
    (fun z => lcpLen q k Tq Tk (b - z) c) 1 (b - a)
    (top_mismatch_zero_of_open hQ hK hne hopen hab)

/-! ### Guarded same-symbol left/right adapters -/

/-- The left-edge certificate with guarded recursive parameter `leftCtx`.
Unlike `BoundaryRangeCount.left_edge_certificate`, this needs neither `0 < ap`
nor `0 < c`. -/
def leftEdgeCertificateGuarded
    {q k : Nat → α} {Tq Tk ap bp c d : Nat} {αs' βs : α}
    (hQp : ConstRun q Tq ap bp αs') (hK : ConstRun k Tk c d βs)
    (heq : αs' = βs) (hab : ap ≤ bp) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcsLen q k bp (c + z - 1)) where
  lo := 1
  spike := bp - ap + 1
  hi := d - c
  gamma := Repair.leftCtx q k ap c
  shape := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz1 hz hzn
      have h := RunRect.run_rectangle_offset_gt
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := ap) (b := bp) (c := c) (d := d)
        (αs := αs') (βs := βs) hQp hK heq
        (t := bp) (e := c + z - 1)
        hab (Nat.le_refl bp) (by omega) (by omega) (by omega)
      have he : (c + z - 1) - c + 1 = z := by omega
      rw [he] at h
      simpa using h
    · intro z hz1 hz hzn
      subst z
      by_cases hpos : 0 < ap ∧ 0 < c
      · have h := RunRect.run_rectangle_offset_eq
          (q := q) (k := k) (Tq := Tq) (Tk := Tk)
          (a := ap) (b := bp) (c := c) (d := d)
          (αs := αs') (βs := βs) hQp hK heq
          hpos.1 hpos.2 (t := bp) (e := c + (bp - ap + 1) - 1)
          hab (Nat.le_refl bp) (by omega) (by omega) (by omega)
        have hleft : Repair.leftCtx q k ap c = lcsLen q k (ap - 1) (c - 1) :=
          Repair.leftCtx_eq (q := q) (k := k) hpos.1 hpos.2
        rw [← hleft] at h
        simpa using h
      · have hbase : ap = 0 ∨ c = 0 := by omega
        have h := BoundaryCertificates.run_rectangle_offset_eq_base
          (q := q) (k := k) (Tq := Tq) (Tk := Tk)
          (a := ap) (b := bp) (c := c) (d := d)
          (αs := αs') (βs := βs) hQp hK heq hbase
          (t := bp) (e := c + (bp - ap + 1) - 1)
          hab (Nat.le_refl bp) (by omega) (by omega) (by omega)
        have hleft : Repair.leftCtx q k ap c = 0 :=
          Repair.leftCtx_zero (q := q) (k := k) hbase
        rw [hleft, Nat.add_zero]
        exact h
    · intro z hz1 hz hzn
      have h := RunRect.run_rectangle_offset_lt
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := ap) (b := bp) (c := c) (d := d)
        (αs := αs') (βs := βs) hQp hK heq
        (t := bp) (e := c + z - 1)
        hab (Nat.le_refl bp) (by omega) (by omega) (by omega)
      simpa using h

/-- The right-edge certificate with the named guarded parameter `rightCtx`.
The definition is the existing certificate with only its gamma field exposed
through the canonical context accessor. -/
def rightEdgeCertificateGuarded
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (heq : αs = βs) (hab : a ≤ b) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk a (d - z)) where
  lo := 0
  spike := b - a
  hi := d - c
  gamma := Repair.rightCtx q k Tq Tk b d
  shape := by
    have h := (BoundaryRangeCount.right_edge_certificate
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := a) (b := b) (c := c) (d := d)
        (αs := αs) (βs := βs) hQ hK heq hab hcd).shape
    simpa [BoundaryRangeCount.right_edge_certificate, Repair.rightCtx] using h

/-! ### Exact mismatch certificates on the closed right/top edges -/

def rightCornerSpikeCertificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hopen : c < d → a < b) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk a (d - z)) :=
  cornerSpikeEdgeCertificate
    (fun z => lcpLen q k Tq Tk a (d - z)) (d - c)
    (lcpLen q k Tq Tk a d) (by simp)
    (right_mismatch_zero_of_open hQ hK hne hopen hcd)

def topCornerSpikeCertificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hopen : a < b → c < d) (hab : a ≤ b) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (b - z) c) :=
  cornerSpikeEdgeCertificate
    (fun z => lcpLen q k Tq Tk (b - z) c) (b - a)
    (lcpLen q k Tq Tk b c) (by simp)
    (top_mismatch_zero_of_open hQ hK hne hopen hab)

/-! ### Symbol-case adapters used by the concrete run assembly -/

def leftCertificateOrZero
    {q k : Nat → α} {Tq Tk ap bp c d : Nat} {αs' βs : α}
    (hQp : ConstRun q Tq ap bp αs') (hK : ConstRun k Tk c d βs)
    (hab : ap ≤ bp) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcsLen q k bp (c + z - 1)) := by
  by_cases heq : αs' = βs
  · exact leftEdgeCertificateGuarded hQp hK heq hab hcd
  · exact leftZeroCertificate hQp hK heq hab hcd

def bottomCertificateOrZero
    {q k : Nat → α} {Tq Tk a b cp dp : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hKprev : ConstRun k Tk cp dp βs)
    (hab : a ≤ b) (hcpd : cp ≤ dp) :
    EdgeRspCertificate (fun z => lcsLen q k (a + z - 1) dp) := by
  by_cases heq : αs = βs
  · exact BoundaryCertificates.bottom_edge_certificate
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (cp := cp) (dp := dp)
      (αs := αs) (βs := βs) hQ hKprev heq hab hcpd
  · exact bottomZeroCertificate hQ hKprev heq hab hcpd

def rightCertificateOrCornerSpike
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hopen : c < d → a < b) (hab : a ≤ b) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk a (d - z)) := by
  by_cases heq : αs = βs
  · exact rightEdgeCertificateGuarded hQ hK heq hab hcd
  · exact rightCornerSpikeCertificate hQ hK heq hopen hcd

def topCertificateOrCornerSpike
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hopen : a < b → c < d) (hab : a ≤ b) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (b - z) c) := by
  by_cases heq : αs = βs
  · exact BoundaryCertificates.top_edge_certificate
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d)
      (αs := αs) (βs := βs) hQ hK heq hab hcd
  · exact topCornerSpikeCertificate hQ hK heq hopen hab

/-! ### Complete run adjacency with symbol cases -/

/-- Six consecutive maximal runs around one mismatch rectangle.  Unlike
`StringBoundaryRuns`, the four adjacent symbols are not required to match.
On each positive-length right/top open edge, the next run is required to be
non-singleton.  This is exactly the region where a symbol mismatch has a zero
spike at the corner and remains constant-zero on the open edge.

The structure starts from an already extracted six-run interior window.  A
concrete string-end extractor still has to supply the two open-edge guards;
this is kept separate from the RSP construction. -/
structure BoundaryRunsComplete (q k : Nat → α) (Tq Tk : Nat) where
  prevQLo : Nat
  prevQHi : Nat
  curQLo : Nat
  curQHi : Nat
  nextQLo : Nat
  nextQHi : Nat
  prevKLo : Nat
  prevKHi : Nat
  curKLo : Nat
  curKHi : Nat
  nextKLo : Nat
  nextKHi : Nat
  αprev : α
  αcur : α
  αnext : α
  βprev : α
  βcur : α
  βnext : α
  hPrevQ : ConstRun q Tq prevQLo prevQHi αprev
  hCurQ : ConstRun q Tq curQLo curQHi αcur
  hNextQ : ConstRun q Tq nextQLo nextQHi αnext
  hPrevK : ConstRun k Tk prevKLo prevKHi βprev
  hCurK : ConstRun k Tk curKLo curKHi βcur
  hNextK : ConstRun k Tk nextKLo nextKHi βnext
  prevQ_nonempty : prevQLo ≤ prevQHi
  curQ_nonempty : curQLo ≤ curQHi
  nextQ_nonempty : nextQLo ≤ nextQHi
  prevK_nonempty : prevKLo ≤ prevKHi
  curK_nonempty : curKLo ≤ curKHi
  nextK_nonempty : nextKLo ≤ nextKHi
  prevQ_adj : prevQHi + 1 = curQLo
  nextQ_adj : curQHi + 1 = nextQLo
  prevK_adj : prevKHi + 1 = curKLo
  nextK_adj : curKHi + 1 = nextKLo
  right_open_guard : curKLo < curKHi → nextQLo < nextQHi
  top_open_guard : curQLo < curQHi → nextKLo < nextKHi
  mismatch : αcur ≠ βcur

namespace BoundaryRunsComplete

variable {q k : Nat → α} {Tq Tk : Nat}

/-- Complete four-edge assembly with all sixteen same/mismatch symbol cases.
The left/bottom mismatch branches are constant zero on their open-edge domains.
The right/top mismatch branches use the exact zero-corner spike. -/
def certificate (r : BoundaryRunsComplete q k Tq Tk) :
    BoundaryRspCertificate
      (fun z => lcsLen q k r.prevQHi (r.curKLo + z - 1))
      (fun z => lcsLen q k (r.curQLo + z - 1) r.prevKHi)
      (fun z => lcpLen q k Tq Tk r.nextQLo (r.curKHi - z))
      (fun z => lcpLen q k Tq Tk (r.curQHi - z) r.nextKLo) :=
  BoundaryCertificates.four_edge_certificate
    (leftCertificateOrZero
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (ap := r.prevQLo) (bp := r.prevQHi)
      (c := r.curKLo) (d := r.curKHi)
      (αs' := r.αprev) (βs := r.βcur)
      r.hPrevQ r.hCurK r.prevQ_nonempty r.curK_nonempty)
    (bottomCertificateOrZero
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := r.curQLo) (b := r.curQHi)
      (cp := r.prevKLo) (dp := r.prevKHi)
      (αs := r.αcur) (βs := r.βprev)
      r.hCurQ r.hPrevK r.curQ_nonempty r.prevK_nonempty)
    (rightCertificateOrCornerSpike
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := r.nextQLo) (b := r.nextQHi)
      (c := r.curKLo) (d := r.curKHi)
      (αs := r.αnext) (βs := r.βcur)
      r.hNextQ r.hCurK r.right_open_guard r.nextQ_nonempty r.curK_nonempty)
    (topCertificateOrCornerSpike
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := r.curQLo) (b := r.curQHi)
      (c := r.nextKLo) (d := r.nextKHi)
      (αs := r.αcur) (βs := r.βnext)
      r.hCurQ r.hNextK r.top_open_guard r.curQ_nonempty r.nextK_nonempty)

/-! ### Exact causal clipping for the four edge coordinates -/

/-- Left edge: `u = curKLo + z - 1` and `p = curQLo`. -/
def LeftCausalClipped (p c z : Nat) : Prop := c + z ≤ p

/-- Right edge: `p = curQHi` and `u = curKHi - z`. -/
def RightCausalClipped (b d z : Nat) : Prop := d < b + z

theorem left_causal_clip_iff (r : BoundaryRunsComplete q k Tq Tk) (z : Nat)
    (hz : 1 ≤ z) :
    r.curKLo + z - 1 < r.curQLo ↔
      LeftCausalClipped r.curQLo r.curKLo z := by
  unfold LeftCausalClipped
  omega

theorem right_causal_clip_iff (r : BoundaryRunsComplete q k Tq Tk) (z : Nat)
    (hz : z ≤ r.curKHi) :
    r.curKHi - z < r.curQHi ↔
      RightCausalClipped r.curQHi r.curKHi z := by
  unfold RightCausalClipped
  omega

theorem bottom_causal_clip_iff (r : BoundaryRunsComplete q k Tq Tk) (z : Nat)
    (hz : 1 ≤ z) :
    r.curKLo < r.curQLo + z - 1 ↔
      BoundaryCertificates.BottomCausalLo r.curQLo r.prevKHi ≤ z := by
  have h := BoundaryCertificates.bottom_causal_clip_iff
    (a := r.curQLo) (dp := r.prevKHi) (z := z) hz
  simpa [r.prevK_adj] using h

theorem top_causal_clip_iff (r : BoundaryRunsComplete q k Tq Tk) (z : Nat) :
    r.nextKLo - 1 < r.curQHi - z ↔
      BoundaryCertificates.TopCausalClipped r.curQHi r.nextKLo z := by
  have hpos : 0 < r.nextKLo := by
    rw [← r.nextK_adj]
    omega
  exact BoundaryCertificates.top_causal_clip_iff
    (b := r.curQHi) (c := r.nextKLo) (z := z) hpos

/-- The four actual run-adjacency relations each satisfy the exhaustive
same/different split used by the corresponding certificate adapter. -/
theorem adjacent_symbol_cases (r : BoundaryRunsComplete q k Tq Tk) :
    (r.αprev = r.βcur ∨ r.αprev ≠ r.βcur) ∧
    (r.αcur = r.βprev ∨ r.αcur ≠ r.βprev) ∧
    (r.αnext = r.βcur ∨ r.αnext ≠ r.βcur) ∧
    (r.αcur = r.βnext ∨ r.αcur ≠ r.βnext) := by
  constructor
  · by_cases h : r.αprev = r.βcur
    · exact Or.inl h
    · exact Or.inr h
  · constructor
    · by_cases h : r.αcur = r.βprev
      · exact Or.inl h
      · exact Or.inr h
    · constructor
      · by_cases h : r.αnext = r.βcur
        · exact Or.inl h
        · exact Or.inr h
      · by_cases h : r.αcur = r.βnext
        · exact Or.inl h
        · exact Or.inr h

/-- Seven-range counting for the complete same/mismatch assembly. -/
theorem certificate_range_count_le_seven
    (r : BoundaryRunsComplete q k Tq Tk)
    (thrLeft thrBottom thrRight thrTop : Nat)
    (windowLo windowHi runLo runHi : Nat) :
    rangeCount
      (BoundaryRangePlan.effectiveCuts
        { records := r.certificate.toRecords thrLeft thrBottom thrRight thrTop
          windowLo := windowLo
          windowHi := windowHi
          runLo := runLo
          runHi := runHi }) ≤ 7 :=
  BoundaryRangeCount.boundary_rsp_certificate_range_count_le_seven
    r.certificate thrLeft thrBottom thrRight thrTop windowLo windowHi runLo runHi

end BoundaryRunsComplete

end BoundaryZeroCertificates

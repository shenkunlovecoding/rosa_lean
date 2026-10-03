import BoundaryRangeCount

/-!
## Real four-edge RSP certificates

`BoundaryRangeCount` supplies the counting core and the existing left/right
string-level certificates.  This file adds the two remaining boundary
orientations:

* bottom edge `u = B.end + 1`: the left context is an LCS RSP while the Q
  centre moves through its current run;
* top edge `u = C.start - 1`: the right context is an LCP RSP, read forward
  into the next K run, while the Q centre moves backwards through its run.

The certificates are pure string facts.  Causal clipping (`u < p`, as in a
ROSA one-bit centre) is kept out of their hypotheses and exposed separately by
`BottomCausalLo`/`TopCausalClipped`; callers pass the resulting one-dimensional
window to `BoundaryRangePlan`.
-/

open Lcs RunRect Repair RspSummary RunRectLcp

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace BoundaryCertificates

open BoundaryRangeCount

variable {α : Type} [DecidableEq α]

/-! ### The missing zero-predecessor case for the LCS rectangle -/

/-- The equal-offset LCS rectangle formula when one diagonal predecessor is the
empty prefix.  This is the `a = 0 ∨ c = 0` base case needed to define the
bottom-edge certificate without artificial positivity assumptions. -/
theorem run_rectangle_offset_eq_base
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (heq : αs = βs) (hbase : a = 0 ∨ c = 0)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b)
    (he : c ≤ e) (hed : e ≤ d) (hxy : t - a = e - c) :
    lcsLen q k t e = t - a + 1 := by
  rcases hbase with ha | hc
  · subst a
    apply lcsLen_eq_of
    · refine ⟨by omega, by omega, ?_⟩
      intro h hh
      rw [List.mem_range] at hh
      have hqt : q (t - h) = αs := hQ.mem (t - h) (by omega) (by omega)
      have hke : k (e - h) = βs := hK.mem (e - h) (by omega) (by omega)
      rw [hqt, hke, heq]
    · intro hcon
      have := hcon.1
      omega
  · subst c
    apply lcsLen_eq_of
    · refine ⟨by omega, by omega, ?_⟩
      intro h hh
      rw [List.mem_range] at hh
      have hqt : q (t - h) = αs := hQ.mem (t - h) (by omega) (by omega)
      have hke : k (e - h) = βs := hK.mem (e - h) (by omega) (by omega)
      rw [hqt, hke, heq]
    · intro hcon
      have := hcon.2.1
      omega

/-! ### Bottom edge: `u = B.end + 1`, varying Q -/

/-- Bottom-edge L certificate.  `hQ` is the current Q run.  `hKprev` is the
maximal K run immediately before the current K run; hence its `end + 1` is the
bottom coordinate.  The offset is `z = p - a + 1`, and the spike is the length
of `hKprev`.  The recursive `γ` is guarded by `Repair.leftCtx`, so the formula
also covers a zero-length diagonal predecessor. -/
def bottom_edge_certificate
    {q k : Nat → α} {Tq Tk a b cp dp : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hKprev : ConstRun k Tk cp dp βs)
    (heq : αs = βs) (hab : a ≤ b) (hcpd : cp ≤ dp) :
    EdgeRspCertificate (fun z => lcsLen q k (a + z - 1) dp) where
  lo := 1
  spike := dp - cp + 1
  hi := b - a + 1
  gamma := Repair.leftCtx q k a cp
  shape := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz1 hz hzn
      have hofflt : (a + z - 1) - a < dp - cp := by omega
      have h := RunRect.run_rectangle_offset_lt
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := a) (b := b) (c := cp) (d := dp) (αs := αs) (βs := βs)
        hQ hKprev heq (by omega) (by omega) hcpd (Nat.le_refl dp) hofflt
      have harg : (a + z - 1) - a + 1 = z := by omega
      rw [harg] at h
      simpa using h
    · intro z hz1 hz hzn
      subst z
      have hoffeq : (a + (dp - cp + 1) - 1) - a = dp - cp := by omega
      by_cases hpos : 0 < a ∧ 0 < cp
      · have h := RunRect.run_rectangle_offset_eq
          (q := q) (k := k) (Tq := Tq) (Tk := Tk)
          (a := a) (b := b) (c := cp) (d := dp) (αs := αs) (βs := βs)
          hQ hKprev heq hpos.1 hpos.2 (by omega) (by omega) hcpd
          (Nat.le_refl dp) hoffeq
        have hleft : Repair.leftCtx q k a cp = lcsLen q k (a - 1) (cp - 1) :=
          Repair.leftCtx_eq (q := q) (k := k) hpos.1 hpos.2
        rw [hleft]
        have harg : (a + (dp - cp + 1) - 1) - a + 1 = dp - cp + 1 := by omega
        rw [harg] at h
        simpa using h
      · have hbase : a = 0 ∨ cp = 0 := by omega
        have h := run_rectangle_offset_eq_base
          (q := q) (k := k) (Tq := Tq) (Tk := Tk)
          (a := a) (b := b) (c := cp) (d := dp) (αs := αs) (βs := βs)
          hQ hKprev heq hbase (by omega) (by omega) hcpd (Nat.le_refl dp) hoffeq
        have hleft : Repair.leftCtx q k a cp = 0 :=
          Repair.leftCtx_zero (q := q) (k := k) hbase
        rw [hleft, Nat.add_zero]
        have harg : (a + (dp - cp + 1) - 1) - a + 1 = dp - cp + 1 := by omega
        rw [harg] at h
        simpa using h
    · intro z hz1 hz hzn
      have hoffgt : dp - cp < (a + z - 1) - a := by omega
      have h := RunRect.run_rectangle_offset_gt
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := a) (b := b) (c := cp) (d := dp) (αs := αs) (βs := βs)
        hQ hKprev heq (by omega) (by omega) hcpd (Nat.le_refl dp) hoffgt
      simpa using h

/-! ### Top edge: `u = C.start - 1`, reflected Q -/

/-- Top-edge R certificate.  `hQ` is the current Q run and `hKnext` is the
maximal K run immediately after the current K run.  The offset is `z = b - p`;
the context reads forward from K's next-run start, and the spike is the length
of `hKnext`. -/
def top_edge_certificate
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hKnext : ConstRun k Tk c d βs)
    (heq : αs = βs) (hab : a ≤ b) (hcd : c ≤ d) :
    EdgeRspCertificate (fun z => lcpLen q k Tq Tk (b - z) c) where
  lo := 0
  spike := d - c
  hi := b - a
  gamma := lcpLen q k Tq Tk b d
  shape := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz0 hz hzn
      have h := RunRectLcp.repair_edge_right_rsp
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := a) (b := b) (c := c) (d := d) (αs := αs) (βs := βs)
        hQ hKnext heq (p := b - z) (u := c) (by omega) (by omega) (Nat.le_refl c) hcd
      have hp : b - (b - z) = z := by omega
      rw [hp] at h
      rw [if_pos hz] at h
      simpa using h
    · intro z hz0 hz hzn
      subst z
      have h := RunRectLcp.repair_edge_right_rsp
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := a) (b := b) (c := c) (d := d) (αs := αs) (βs := βs)
        hQ hKnext heq (p := b - (d - c)) (u := c) (by omega) (by omega)
        (Nat.le_refl c) hcd
      have hp : b - (b - (d - c)) = d - c := by omega
      rw [hp] at h
      rw [if_neg (by omega : ¬ d - c < d - c)] at h
      rw [if_pos rfl] at h
      simpa using h
    · intro z hz0 hz hzn
      have h := RunRectLcp.repair_edge_right_rsp
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := a) (b := b) (c := c) (d := d) (αs := αs) (βs := βs)
        hQ hKnext heq (p := b - z) (u := c) (by omega) (by omega) (Nat.le_refl c) hcd
      have hp : b - (b - z) = z := by omega
      rw [hp] at h
      rw [if_neg (by omega : ¬ z < d - c)] at h
      rw [if_neg (by omega : ¬ z = d - c)] at h
      simpa using h

/-! ### Causal clipping interfaces -/

/-- `u < p` is the only extra condition needed by the ROSA bridge layer.  For
the bottom edge, `u = dp + 1` and `p = a + z - 1`, so clipping lowers the
certificate offset domain to this bound. -/
def BottomCausalLo (a dp : Nat) : Nat := max 1 (dp + 3 - a)

/-- Exact bottom-edge causal clipping condition. -/
theorem bottom_causal_clip_iff {a dp z : Nat} (hz : 1 ≤ z) :
    dp + 1 < a + z - 1 ↔ BottomCausalLo a dp ≤ z := by
  unfold BottomCausalLo
  omega

/-- On the top edge, `u = c - 1` and `p = b - z`; causal clipping is the
exact predicate `z + c ≤ b`.  A `Nat` upper bound would incorrectly saturate
when the next K run starts to the right of the current Q run. -/
def TopCausalClipped (b c z : Nat) : Prop := z + c ≤ b

/-- Exact top-edge causal clipping condition. -/
theorem top_causal_clip_iff {b c z : Nat} (hc : 0 < c) :
    c - 1 < b - z ↔ TopCausalClipped b c z := by
  unfold TopCausalClipped
  omega

/-! ### Four-edge assembly -/

/-- Package the four proof-carrying edge certificates as the public boundary
certificate consumed by the seven-range counting theorem. -/
def four_edge_certificate
    {fLeft fBottom fRight fTop : Nat → Nat}
    (left : EdgeRspCertificate fLeft) (bottom : EdgeRspCertificate fBottom)
    (right : EdgeRspCertificate fRight) (top : EdgeRspCertificate fTop) :
    BoundaryRspCertificate fLeft fBottom fRight fTop where
  left := left
  bottom := bottom
  right := right
  top := top

/-- The counting theorem instantiated with an explicitly assembled four-edge
certificate.  `windowLo`/`windowHi` are the caller-supplied causal/owner clip;
the pure certificate construction does not smuggle in `u < p`. -/
theorem boundary_rsp_certificate_range_count_le_seven
    {fLeft fBottom fRight fTop : Nat → Nat}
    (cert : BoundaryRspCertificate fLeft fBottom fRight fTop)
    (thrLeft thrBottom thrRight thrTop : Nat)
    (windowLo windowHi runLo runHi : Nat) :
    rangeCount
      (BoundaryRangePlan.effectiveCuts
        { records := cert.toRecords thrLeft thrBottom thrRight thrTop
          windowLo := windowLo
          windowHi := windowHi
          runLo := runLo
          runHi := runHi }) ≤ 7 :=
  BoundaryRangeCount.boundary_rsp_certificate_range_count_le_seven
    cert thrLeft thrBottom thrRight thrTop windowLo windowHi runLo runHi

/-- Same bound after assembling the four certificates from their individual
proofs. -/
theorem four_edge_boundary_rsp_certificate_range_count_le_seven
    {fLeft fBottom fRight fTop : Nat → Nat}
    (left : EdgeRspCertificate fLeft) (bottom : EdgeRspCertificate fBottom)
    (right : EdgeRspCertificate fRight) (top : EdgeRspCertificate fTop)
    (thrLeft thrBottom thrRight thrTop : Nat)
    (windowLo windowHi runLo runHi : Nat) :
    rangeCount
      (BoundaryRangePlan.effectiveCuts
        { records :=
            (four_edge_certificate left bottom right top).toRecords
              thrLeft thrBottom thrRight thrTop
          windowLo := windowLo
          windowHi := windowHi
          runLo := runLo
          runHi := runHi }) ≤ 7 :=
  BoundaryRangeCount.boundary_rsp_certificate_range_count_le_seven
    (four_edge_certificate left bottom right top)
    thrLeft thrBottom thrRight thrTop windowLo windowHi runLo runHi

/-! ### Concrete six-run interface around one mismatch rectangle -/

/-- The six maximal runs needed by the four real edge certificates:

* `prevQ, curQ, nextQ` are the maximal Q runs;
* `prevK, curK, nextK` are the maximal K runs;
* the four adjacency fields say that the six runs meet consecutively.

The four match fields identify the adjacent run used by each edge.  The pure
certificate construction itself is valid without `curQ`/`curK` being a mismatch
rectangle; `mismatch` records that intended ROSA use. -/
structure StringBoundaryRuns (q k : Nat → α) (Tq Tk : Nat) where
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
  prevQ_pos : 0 < prevQLo
  curK_pos : 0 < curKLo
  left_match : αprev = βcur
  right_match : αnext = βcur
  bottom_match : αcur = βprev
  top_match : αcur = βnext
  prevQ_adj : prevQHi + 1 = curQLo
  nextQ_adj : curQHi + 1 = nextQLo
  prevK_adj : prevKHi + 1 = curKLo
  nextK_adj : curKHi + 1 = nextKLo
  mismatch : αcur ≠ βcur

namespace StringBoundaryRuns

variable {q k : Nat → α} {Tq Tk : Nat}

/-- The real four-edge string certificate.  The function arguments record the
exact owner/opposite-run prefix read by each edge:

* left: previous Q run against current K run;
* bottom: current Q run against previous K run;
* right: next Q run against current K run;
* top: current Q run against next K run. -/
def certificate (r : StringBoundaryRuns q k Tq Tk) :
    BoundaryRspCertificate
      (fun z => lcsLen q k r.prevQHi (r.curKLo + z - 1))
      (fun z => lcsLen q k (r.curQLo + z - 1) r.prevKHi)
      (fun z => lcpLen q k Tq Tk r.nextQLo (r.curKHi - z))
      (fun z => lcpLen q k Tq Tk (r.curQHi - z) r.nextKLo) :=
  four_edge_certificate
    (BoundaryRangeCount.left_edge_certificate
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (ap := r.prevQLo) (bp := r.prevQHi)
      (c := r.curKLo) (d := r.curKHi)
      (αs' := r.αprev) (βs := r.βcur)
      r.hPrevQ r.hCurK r.left_match r.prevQ_nonempty r.prevQ_pos
      r.curK_pos r.curK_nonempty)
    (bottom_edge_certificate
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := r.curQLo) (b := r.curQHi)
      (cp := r.prevKLo) (dp := r.prevKHi)
      (αs := r.αcur) (βs := r.βprev)
      r.hCurQ r.hPrevK r.bottom_match r.curQ_nonempty r.prevK_nonempty)
    (BoundaryRangeCount.right_edge_certificate
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := r.nextQLo) (b := r.nextQHi)
      (c := r.curKLo) (d := r.curKHi)
      (αs := r.αnext) (βs := r.βcur)
      r.hNextQ r.hCurK r.right_match r.nextQ_nonempty r.curK_nonempty)
    (top_edge_certificate
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := r.curQLo) (b := r.curQHi)
      (c := r.nextKLo) (d := r.nextKHi)
      (αs := r.αcur) (βs := r.βnext)
      r.hCurQ r.hNextK r.top_match r.curQ_nonempty r.nextK_nonempty)

/-- Seven-range counting theorem instantiated by the concrete four-edge string
certificate.  `windowLo`/`windowHi` are the causal clip supplied by the caller;
the certificate layer deliberately does not assume `u < p`. -/
theorem certificate_range_count_le_seven
    (r : StringBoundaryRuns q k Tq Tk)
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

end StringBoundaryRuns


end BoundaryCertificates

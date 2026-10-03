import Std
import Route
import QCut
import RosBridge

/-!
## Phase H (new) — step 2: an active Q-bridge beats the Q deletion baseline

A repair bridge born at its Q-owner `p` has active length
`ℓ(t) = L+1+(t-p) ≥ 1+(t-p)`, while the Q-cut baseline is capped at `t-p`
(`QCut.bruteQCut_len_le`).  Hence every active Q-bridge strictly beats the
baseline, and Q-side repair needs no cut baseline at all.
-/

namespace QBridge
open Route RosBridge
open RosBridge.Bridge

/-- **Active Q-bridge beats the Q-cut baseline.**  (Independent of the row `ell`.) -/
theorem q_bridge_beats_cut (ell : Nat → Int) (b : Bridge) (p t : Nat)
    (hbirth : b.p = p) (ha : b.Active t) :
    rle (QCut.bruteQCut ell t p) (b.routeAt t) := by
  have hpt : p ≤ t := by have := ha.1; omega
  have hcut : (QCut.bruteQCut ell t p).len ≤ (t : Int) - (p : Int) :=
    QCut.bruteQCut_len_le ell t p hpt
  have hlen : (b.routeAt t).len = (b.L : Int) + 1 + ((t : Int) - (b.p : Int)) := by
    simp only [routeAt]
    have hc : ((b.L + 1 + (t - b.p) : Nat) : Int) = (b.L : Int) + 1 + ((t : Int) - (b.p : Int)) := by
      omega
    rw [hc]
  rw [rle]
  left
  omega

end QBridge

import Std
import Route
import Lcs
import RunRectangle
import Repair
import RosBridge

/-!
## Phase H (new) — step 4: strict-interior bulk compression (§7, §8)

By Boundary-Support (`repair_strict_interior_trivial`) a strict-interior one-bit
centre `(a<p<b, c<u<d)` has `L = R = 0`.  So its bridge is born and dies at `t=p`
with value `(1,u)`.  Hence the whole 2-D interior collapses:

* **Q-side (§7, fixed Q-owner `p`)**: the interior K-endpoints only compete at
  `t = p`, all with value `(1,·)`; the best is `u_* = min(d-1, p-1)`.
* **K-side (§8, fixed K-owner `u`)**: the interior Q-centres' births `t = p` range
  exactly over `[max(a+1,u+1), b-1]` — a single constant-route active segment.
-/

namespace Interior
open Route Lcs RunRect Repair RosBridge
open RosBridge.Bridge

/-- Strict-interior, causal one-bit centres (`a<p<b`, `c<u<d`, `u<p`). -/
def interiorCenter (a b c d p u : Nat) : Prop := a < p ∧ p < b ∧ c < u ∧ u < d ∧ u < p

/-- The repair bridge attached to an interior centre. -/
def interiorBridge {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk p u : Nat) : Bridge :=
  ⟨p, u, leftCtx q k p u, rightCtx q k Tq Tk p u⟩

/-- **§7/§8 core.**  An interior bridge is active only at `t = p`, where its route
is `(1,u)` — independent of the centre. -/
theorem interior_bridge_route {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    [DecidableEq α]
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p u : Nat} (hap : a < p) (hpb : p < b) (huc : c < u) (hud : u < d) :
    (interiorBridge q k Tq Tk p u).routeAt p = (⟨1, (u : Int)⟩ : Route) ∧
      (interiorBridge q k Tq Tk p u).death = p := by
  obtain ⟨hL, hR⟩ := repair_strict_interior_trivial hQ hK hne hap hpb huc hud
  have hp0 : 0 < p := by omega
  have hu0 : 0 < u := by omega
  have hLc : leftCtx q k p u = 0 := by rw [leftCtx_eq hp0 hu0, hL]
  have hRc : rightCtx q k Tq Tk p u = 0 := by unfold rightCtx; exact hR
  constructor
  · unfold interiorBridge Bridge.routeAt
    simp only [Nat.sub_self, Nat.add_zero, hLc]
    rfl
  · unfold interiorBridge Bridge.death
    simp only [hRc, Nat.add_zero]

/-- **§8 — K-side interior bulk.**  For a fixed K-owner `u`, the interior centres'
births `t = p` range exactly over `[max(a+1,u+1), b-1]`. -/
theorem k_interior_bulk_equiv {a b c d u t : Nat} (hcu : c < u) (hud : u < d) :
    (∃ p, interiorCenter a b c d p u ∧ t = p) ↔ max (a + 1) (u + 1) ≤ t ∧ t ≤ b - 1 := by
  constructor
  · rintro ⟨p, ⟨ha, hb, _, _, hup⟩, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨t, ⟨by omega, by omega, hcu, hud, by omega⟩, rfl⟩

/-- **§7 — Q-side interior bulk.**  For a fixed Q-owner `p`, every interior
K-endpoint is `≤ u_* = min(d-1, p-1)`. -/
theorem q_interior_bulk_max {c d p : Nat} :
    ∀ u, c < u → u < d → u < p → u ≤ min (d - 1) (p - 1) := by
  intro u h1 h2 h3; omega

/-- §7: the bound `u_* = min(d-1, p-1)` is itself a legal interior endpoint
whenever the interior is non-empty (`c < u_*`). -/
theorem q_interior_bulk_attained {c d p : Nat} (h : c < min (d - 1) (p - 1)) :
    c < min (d - 1) (p - 1) ∧ min (d - 1) (p - 1) < d ∧ min (d - 1) (p - 1) < p := by
  omega

end Interior

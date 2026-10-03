import Std
import Route

/-!
## Phase H (new) — step 1: the `Bridge` semantics layer

A one-bit repair bridge `b = (p,u,L,R)` is active on `[p, p+R]`; its route is
`ℓ(t) = L+1+(t-p)`, `r(t) = u+(t-p)`.  Normalising by
`κ_b = (p-L, -(u-p+1))` makes the ROSA priority **time-independent**, which is
the interface every later skyline theorem needs.
-/

namespace RosBridge
open Route

/-- A one-bit repair bridge: Q-centre `p`, K-centre `u`, left/right contexts. -/
structure Bridge where
  p : Nat
  u : Nat
  L : Nat
  R : Nat
  deriving DecidableEq, Repr

namespace Bridge

/-- Birth point (the route only exists from here). -/
def birth (b : Bridge) : Nat := b.p

/-- Expiry. -/
def death (b : Bridge) : Nat := b.p + b.R

/-- Active lifetime `[p, p+R]`. -/
def Active (b : Bridge) (t : Nat) : Prop := b.p ≤ t ∧ t ≤ b.p + b.R

instance (b : Bridge) (t : Nat) : Decidable (Active b t) := by unfold Active; infer_instance

/-- Bridge route at `t` (§9.1).  Only meaningful under `Active b t`. -/
def routeAt (b : Bridge) (t : Nat) : Route :=
  ⟨((b.L + 1 + (t - b.p) : Nat) : Int), ((b.u + (t - b.p) : Nat) : Int)⟩

/-- Shadow start `a_c = p_c − L_c` (§11): where `c`'s left context begins to
carry its priority through the deletion baseline. -/
def shadowStart (b : Bridge) : Int := (b.p : Int) - (b.L : Int)

/-- Normalised priority `κ_b = (p−L, −(u−p+1))` (smaller is better). -/
def kappa (b : Bridge) : Int × Int :=
  ((b.p : Int) - (b.L : Int), -(((b.u : Int) - (b.p : Int)) + 1))

theorem valid_routeAt (b : Bridge) (t : Nat) (h : b.Active t) : Valid (b.routeAt t) := by
  obtain ⟨hb1, _⟩ := h
  refine ⟨by simp only [routeAt]; omega, by simp only [routeAt]; omega, ?_⟩
  simp only [routeAt]; intro h0; omega

end Bridge

/-- Route priority carried into `κ` coordinates at time `t`. -/
def routeKappa (t : Nat) (r : Route) : Int × Int :=
  ((t : Int) - r.len + 1, -(r.endpoint - (t : Int) + 1))

/-- Lexicographic `≤` on `Int × Int` (Std has no `LinearOrder (Int × Int)`). -/
def klexLE (x y : Int × Int) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

instance (x y : Int × Int) : Decidable (klexLE x y) := by unfold klexLE; infer_instance

theorem klexLE_antisymm {x y : Int × Int} (h1 : klexLE x y) (h2 : klexLE y x) : x = y := by
  unfold klexLE at h1 h2
  apply Prod.ext
  · rcases h1 with h | ⟨h, _⟩ <;> rcases h2 with h' | ⟨h', _⟩ <;> omega
  · rcases h1 with h | ⟨h, h1'⟩ <;> rcases h2 with h' | ⟨h', h2'⟩ <;> omega

/-- **`κ` is constant along a bridge's lifetime** (§4). -/
theorem bridge_kappa_const (b : Bridge) (t : Nat) (h : b.Active t) :
    routeKappa t (b.routeAt t) = b.kappa := by
  obtain ⟨hb1, _⟩ := h
  apply Prod.ext
  · simp only [routeKappa, Bridge.routeAt, Bridge.kappa]
    have hc : ((b.L + 1 + (t - b.p) : Nat) : Int) = (b.L : Int) + 1 + ((t : Int) - (b.p : Int)) := by
      omega
    rw [hc]; omega
  · simp only [routeKappa, Bridge.routeAt, Bridge.kappa]
    have hc : ((b.u + (t - b.p) : Nat) : Int) = (b.u : Int) + ((t : Int) - (b.p : Int)) := by
      omega
    rw [hc]; omega

/-- ROSA route priority at a common time `t` is exactly the `κ` priority (reversed). -/
theorem route_rle_iff_kappa (t : Nat) (a b : Route) :
    Route.rle a b ↔ klexLE (routeKappa t b) (routeKappa t a) := by
  unfold Route.rle klexLE routeKappa
  constructor <;> intro h <;> omega

/-- **Priority ↔ `κ`.**  For two bridges active at the same `t`, `b` beats `c`
in the ROSA route order iff `κ_b ≤ κ_c`. -/
theorem route_better_iff_kappa (b c : Bridge) (t : Nat) (hb : b.Active t) (hc : c.Active t) :
    Route.rle (c.routeAt t) (b.routeAt t) ↔ klexLE b.kappa c.kappa := by
  rw [route_rle_iff_kappa, bridge_kappa_const b t hb, bridge_kappa_const c t hc]

end RosBridge

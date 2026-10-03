import Std
import Route
import Repair
import RosBridge
import OwnerBridges
import Interior

/-!
## Phase H (new) — step 10: fixed-owner compressed candidates

A bridge alone is not enough to represent the compressed field: the **K-side
strict-interior bulk** is a *constant* route on a whole `t`-segment (§8), not a
single bridge.  So we introduce a general candidate

```lean
structure Cand where lo hi : Nat; rt : Nat → Route
```

and compress each fixed-owner collection by geometric region
(§15: strict-interior bulk / edges / corners):

* **Q-side** (`qOwnerCompressed`): the strict-interior K-centres (all with
  `L = R = 0`, birth/expiry `p`) collapse to the single best endpoint `u_*`; the
  K-edge centres `u=c`, `u=d` stay.
* **K-side** (`kOwnerCompressed`): the strict-interior Q-centres form the single
  constant-route candidate `(1,u)` on `[max(a+1,u+1), b-1]` (§8); the Q-edge
  centres stay.

The max-equivalence `field Compressed = field Actual` (step 11) is what remains.
-/

namespace OwnerCompress
open Route Lcs Repair RosBridge OwnerBridges

variable {α : Type} [DecidableEq α]

/-- A candidate repair route: `rt` is active on `[lo, hi]`. -/
structure Cand where
  lo : Nat
  hi : Nat
  rt : Nat → Route

namespace Cand

/-- Active window. -/
def Active (c : Cand) (t : Nat) : Prop := c.lo ≤ t ∧ t ≤ c.hi

end Cand

/-- A bridge, as a candidate (active on `[p, p+R]`). -/
def candOf (b : Bridge) : Cand := ⟨b.p, b.death, b.routeAt⟩

/-- Lift a bridge list to candidates. -/
def candsOf (bs : List Bridge) : List Cand := bs.map candOf

/-- **The candidate field at `t`**: the best route among the active candidates. -/
def field (cs : List Cand) (t : Nat) : Route :=
  rmaxList (cs.map (fun c => if c.lo ≤ t ∧ t ≤ c.hi then c.rt t else unmatched))

/-- The bridge-level field at `t`: the best route among the active bridges. -/
def fieldBridges (bs : List Bridge) (t : Nat) : Route :=
  rmaxList (bs.map (fun b => if b.Active t then b.routeAt t else unmatched))

/-! ### The two bulk delegates -/

/-- §7: the Q-side interior bulk delegate — the best strict-interior K-centre
`u_* = min(d-1, p-1)`, whose birthday is `p`. -/
def qInteriorBulk (q k : Nat → α) (Tq Tk p c d : Nat) : Cand :=
  candOf (mkBridge q k Tq Tk p (min (d - 1) (p - 1)))

/-- §8: the K-side interior bulk delegate — the constant route `(1,u)` on
`[max(a+1,u+1), b-1]`. -/
def kInteriorBulk (a b u : Nat) : Cand :=
  ⟨max (a + 1) (u + 1), b - 1, fun _ => (⟨1, (u : Int)⟩ : Route)⟩

/-! ### Interface lemmas -/

@[simp] theorem candOf_active (b : Bridge) (t : Nat) : (candOf b).Active t ↔ b.Active t :=
  Iff.rfl

@[simp] theorem candOf_birth (b : Bridge) : (candOf b).lo = b.birth := rfl

@[simp] theorem candOf_death (b : Bridge) : (candOf b).hi = b.death := rfl

@[simp] theorem candOf_rt (b : Bridge) (t : Nat) : (candOf b).rt t = b.routeAt t := rfl

@[simp] theorem kInteriorBulk_rt (a b u t : Nat) :
    (kInteriorBulk a b u).rt t = (⟨1, (u : Int)⟩ : Route) := rfl

@[simp] theorem kInteriorBulk_active (a b u t : Nat) :
    (kInteriorBulk a b u).Active t ↔ max (a + 1) (u + 1) ≤ t ∧ t ≤ b - 1 :=
  Iff.rfl

@[simp] theorem qInteriorBulk_birth (q k : Nat → α) (Tq Tk p c d : Nat) :
    (qInteriorBulk q k Tq Tk p c d).lo = p := rfl

/-- The Q-side interior bulk delegate is the `u_*` bridge. -/
theorem qInteriorBulk_rt (q k : Nat → α) (Tq Tk p c d : Nat) (t : Nat) :
    (qInteriorBulk q k Tq Tk p c d).rt t
      = (mkBridge q k Tq Tk p (min (d - 1) (p - 1))).routeAt t := rfl

/-! ### Compressed collections -/

/-- A Q-owner bridge is *kept* unless it is a strict-interior K-centre other
than the collapsed `u_*` (§7). -/
def qOwnerKept (a b c d p : Nat) (x : Bridge) : Bool :=
  decide (¬ (a < p ∧ p < b ∧ c < x.u ∧ x.u < d ∧ x.u ≠ min (d - 1) (p - 1)))

/-- **Q-side compressed candidates** for a fixed Q-owner `p`.  When `p` is a
strict-interior Q-centre (`a<p<b`) the strict-interior K-centres all share
`L = R = 0` and are collapsed to `u_*`; otherwise the whole family is kept. -/
def qOwnerCompressed (q k : Nat → α) (Tq Tk a b c d p : Nat) : List Cand :=
  ((qOwnerBridges q k Tq Tk a b c d p).filter (qOwnerKept a b c d p)).map candOf

/-- A K-owner bridge is *kept* unless it is a strict-interior Q-centre (§8). -/
def kOwnerKept (a b c d u : Nat) (x : Bridge) : Bool :=
  decide (¬ (a < x.p ∧ x.p < b ∧ c < u ∧ u < d))

/-- The kept K-owner bridges (Q-edge centres). -/
def kOwnerKeptList (q k : Nat → α) (Tq Tk a b c d u : Nat) : List Bridge :=
  (kOwnerBridges q k Tq Tk a b c d u).filter (kOwnerKept a b c d u)

/-- The dropped K-owner bridges (strict-interior Q-centres, collapsed to the bulk). -/
def kOwnerDropped (q k : Nat → α) (Tq Tk a b c d u : Nat) : List Bridge :=
  (kOwnerBridges q k Tq Tk a b c d u).filter (fun x => !(kOwnerKept a b c d u x))

/-- **K-side compressed candidates** for a fixed K-owner `u`.  When `u` is a
strict-interior K-centre (`c<u<d`) the strict-interior Q-centres form one
constant-route candidate (§8); the Q-edge centres are kept. -/
def kOwnerCompressed (q k : Nat → α) (Tq Tk a b c d u : Nat) : List Cand :=
  (if c < u ∧ u < d then [kInteriorBulk a b u] else [])
    ++ (kOwnerKeptList q k Tq Tk a b c d u).map candOf

/-- Unfolding of the kept-predicate. -/
theorem kOwnerKept_eq (a b c d u : Nat) (x : Bridge) :
    kOwnerKept a b c d u x = true ↔ ¬ (a < x.p ∧ x.p < b ∧ c < u ∧ u < d) := by
  unfold kOwnerKept; exact decide_eq_true_iff

theorem mem_qOwnerCompressed {q k : Nat → α} {Tq Tk a b c d p : Nat} {x : Cand} :
    x ∈ qOwnerCompressed q k Tq Tk a b c d p ↔
      ∃ y ∈ qOwnerBridges q k Tq Tk a b c d p,
        qOwnerKept a b c d p y = true ∧ x = candOf y := by
  unfold qOwnerCompressed
  rw [List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (List.mem_filter.mp hy).1, (List.mem_filter.mp hy).2, rfl⟩
  · rintro ⟨y, hy, hk, rfl⟩
    exact ⟨y, List.mem_filter.mpr ⟨hy, hk⟩, rfl⟩

/-- Unfolding of the kept-predicate. -/
theorem qOwnerKept_eq (a b c d p : Nat) (y : Bridge) :
    qOwnerKept a b c d p y = true ↔
      ¬ (a < p ∧ p < b ∧ c < y.u ∧ y.u < d ∧ y.u ≠ min (d - 1) (p - 1)) := by
  unfold qOwnerKept
  exact decide_eq_true_iff

theorem kInteriorBulk_mem {q k : Nat → α} {Tq Tk a b c d u : Nat} (h : c < u ∧ u < d) :
    kInteriorBulk a b u ∈ kOwnerCompressed q k Tq Tk a b c d u := by
  unfold kOwnerCompressed
  rw [List.mem_append]
  left
  rw [if_pos h, List.mem_singleton]

theorem mem_kOwnerCompressed_iff {q k : Nat → α} {Tq Tk a b c d u : Nat} {x : Cand} :
    x ∈ kOwnerCompressed q k Tq Tk a b c d u ↔
      (x = kInteriorBulk a b u ∧ c < u ∧ u < d) ∨
      ∃ y ∈ kOwnerBridges q k Tq Tk a b c d u, kOwnerKept a b c d u y = true ∧ x = candOf y := by
  unfold kOwnerCompressed
  by_cases hb : c < u ∧ u < d
  · rw [if_pos hb, List.mem_append, List.mem_map]
    constructor
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact Or.inl ⟨by simpa using hx, hb⟩
      · exact Or.inr ⟨y, (List.mem_filter.mp hy).1, (List.mem_filter.mp hy).2, rfl⟩
    · rintro (⟨hx, _⟩ | ⟨y, hy, hk, rfl⟩)
      · exact Or.inl (by simpa using hx)
      · exact Or.inr ⟨y, List.mem_filter.mpr ⟨hy, hk⟩, rfl⟩
  · rw [if_neg hb, List.nil_append, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Or.inr ⟨y, (List.mem_filter.mp hy).1, (List.mem_filter.mp hy).2, rfl⟩
    · rintro (⟨_, h1, h2⟩ | ⟨y, hy, hk, rfl⟩)
      · exact absurd ⟨h1, h2⟩ hb
      · exact ⟨y, List.mem_filter.mpr ⟨hy, hk⟩, rfl⟩

end OwnerCompress

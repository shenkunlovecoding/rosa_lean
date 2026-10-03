import Std
import OwnerEnvelope
import BridgeEnvelope
import OwnerCorrect
import OwnerCorrectK
import WinnerPieces

/-!
## Fixed-owner templates versus the real bridge collection

`OwnerEnv.runPairTemplates` is only a nine-route *size skeleton*: its arguments
are arbitrary `AffRoute`s and it carries neither the bridge lifetime nor the
fixed-owner restriction.  This file supplies the missing semantic object.

For a fixed owner, a template is an `OwnerCompress.Cand` (route plus active
interval).  The two template lists below are therefore the corrected owner
templates:

* `qOwnerTemplates`: the kept Q-owner bridges, with the strict-interior
  K-centres collapsed to the single endpoint `min (d-1) (p-1)`;
* `kOwnerTemplates`: the kept K-owner bridges plus the K-side interior bulk
  candidate on `[max (a+1) (u+1), b-1]`.

The main theorems prove that their pointwise route maxima are exactly the raw
bridge maxima, including lifetimes.  It is deliberately *not* claimed that the
old nine-slot list is semantically complete.
-/

namespace OwnerTemplateEquivalence

open Route RosBridge OwnerBridges OwnerCompress OwnerEnv
open Lcs RunRect Repair OwnerCorrect OwnerCorrectK WinnerPieces

variable {α : Type} [DecidableEq α]

/-! ### Fields -/

/-- The real fixed-owner bridge field: the route maximum over active bridges. -/
abbrev actualField (bs : List Bridge) (t : Nat) : Route :=
  OwnerCompress.fieldBridges bs t

/-- A template field: the route maximum over active template candidates. -/
abbrev templateField (cs : List Cand) (t : Nat) : Route :=
  OwnerCompress.field cs t

/-- Corrected Q-owner templates.  The list itself is the exact compressed owner
collection, not a list of unrelated `AffRoute` slots. -/
abbrev qOwnerTemplates (q k : Nat → α) (Tq Tk a b c d p : Nat) : List Cand :=
  OwnerCompress.qOwnerCompressed q k Tq Tk a b c d p

/-- Corrected K-owner templates. -/
abbrev kOwnerTemplates (q k : Nat → α) (Tq Tk a b c d u : Nat) : List Cand :=
  OwnerCompress.kOwnerCompressed q k Tq Tk a b c d u

/-- The corrected template list for a fixed-owner query. -/
def queryTemplates (Q : Query) (q k : Nat → α) (Tq Tk : Nat) : List Cand :=
  match Q.isQ with
  | true => qOwnerTemplates q k Tq Tk Q.a Q.b Q.c Q.d Q.owner
  | false => kOwnerTemplates q k Tq Tk Q.a Q.b Q.c Q.d Q.owner

/-- The real bridge field of a fixed-owner query. -/
abbrev queryActualField (Q : Query) (q k : Nat → α) (Tq Tk : Nat) (t : Nat) : Route :=
  actualField (Q.bridges q k Tq Tk) t

/-- The corrected template field of a fixed-owner query. -/
abbrev queryTemplateField (Q : Query) (q k : Nat → α) (Tq Tk : Nat) (t : Nat) : Route :=
  templateField (queryTemplates Q q k Tq Tk) t

/-- The corrected replacement for the semantic content of `runPairTemplates`.
The old nine-slot definition remains a size skeleton; this list carries exact
owners and active intervals. -/
abbrev runPairOwnerTemplates (Q : Query) (q k : Nat → α) (Tq Tk : Nat) : List Cand :=
  queryTemplates Q q k Tq Tk

/-! ### Owner/output affine coordinates

A bridge is a slope-`(1,1)` route in the output coordinate `t`.  The fixed
owner coordinate `p` enters only in the two intercepts; the K/output coordinate
`u` enters the endpoint intercept. -/

/-- The affine route of a bridge, expressed in its owner/output coordinates. -/
def bridgeAffine (b : Bridge) : AffEnv.AffRoute :=
  OwnerEnv.bridgeRoute (b.L : Int) (b.u : Int) (b.p : Int)

/-- Owner/output form of a bridge route:
`len(owner,t) = t + L + 1 - owner`, `end(owner,t) = t + u - owner`. -/
theorem bridgeAffine_owner_output (b : Bridge) (t : Int) :
    (bridgeAffine b).len t = t + ((b.L : Int) + 1 - (b.p : Int)) ∧
      (bridgeAffine b).ep t = t + ((b.u : Int) - (b.p : Int)) := by
  constructor <;>
    simp only [bridgeAffine, OwnerEnv.bridgeRoute, AffEnv.AffRoute.len,
      AffEnv.AffRoute.ep] <;> omega

/-- On its active interval, the bridge route is exactly the affine
owner/output primitive. -/
theorem bridgeAffine_apply_eq_routeAt (b : Bridge) (t : Nat) (h : b.Active t) :
    (⟨(bridgeAffine b).len (t : Int), (bridgeAffine b).ep (t : Int)⟩ : Route) =
      b.routeAt t := by
  simpa [bridgeAffine, OwnerEnv.bridgeRoute, AffineLifetime.ofBridge] using
    (AffineLifetime.ofBridge_routeAt_eq b t h)

/-- The K-side interior bulk is a constant affine output primitive `(1,u)` on
its active interval. -/
theorem kInteriorBulk_output (a b u t : Nat)
    (h : max (a + 1) (u + 1) ≤ t ∧ t ≤ b - 1) :
    OwnerCorrectK.bulkRoute a b u t = (⟨1, (u : Int)⟩ : Route) := by
  unfold OwnerCorrectK.bulkRoute
  rw [if_pos h]

/-! ### Exact fixed-owner template equivalence -/

/-- **Q-owner template equivalence.**  The corrected template field is the true
active bridge maximum for every fixed Q-owner `p`. -/
theorem qOwnerTemplates_max_eq_actual {q k : Nat → α}
    {Tq Tk a b c d p : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) :
    ∀ t, templateField (qOwnerTemplates q k Tq Tk a b c d p) t =
      actualField (OwnerBridges.qOwnerBridges q k Tq Tk a b c d p) t := by
  intro t
  simpa [templateField, actualField, qOwnerTemplates] using
    (OwnerCorrect.qOwnerCompressed_field
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d) (p := p)
      hQ hK hne t)

/-- **K-owner template equivalence.**  Unlike the existing strict-interior
theorem, this also covers boundary and out-of-range owners.  In the non-strict
case the bulk slot is absent and every actual bridge is kept. -/
theorem kOwnerTemplates_max_eq_actual {q k : Nat → α}
    {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) :
    ∀ t, templateField (kOwnerTemplates q k Tq Tk a b c d u) t =
      actualField (OwnerBridges.kOwnerBridges q k Tq Tk a b c d u) t := by
  intro t
  by_cases hstrict : c < u ∧ u < d
  · simpa [templateField, actualField, kOwnerTemplates] using
      (OwnerCorrectK.kOwnerCompressed_field
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := a) (b := b) (c := c) (d := d) (u := u)
        hQ hK hne hstrict.1 hstrict.2 t)
  · have hfilter : OwnerCompress.kOwnerKeptList q k Tq Tk a b c d u =
        OwnerBridges.kOwnerBridges q k Tq Tk a b c d u := by
      unfold OwnerCompress.kOwnerKeptList
      apply List.filter_eq_self.mpr
      intro x hx
      rw [OwnerCompress.kOwnerKept_eq]
      intro hcore
      exact hstrict ⟨hcore.2.2.1, hcore.2.2.2⟩
    have hcomp : kOwnerTemplates q k Tq Tk a b c d u =
        OwnerCompress.candsOf
          (OwnerBridges.kOwnerBridges q k Tq Tk a b c d u) := by
      unfold kOwnerTemplates OwnerCompress.kOwnerCompressed OwnerCompress.candsOf
      rw [if_neg hstrict, hfilter]
      simp
    rw [hcomp]
    exact OwnerCorrect.field_candsOf
      (OwnerBridges.kOwnerBridges q k Tq Tk a b c d u) t

/-- The corrected template field for a fixed owner/query is exactly the real
bridge field. -/
theorem queryTemplates_max_eq_actual {Q : Query} {q k : Nat → α}
    {Tq Tk : Nat} {αs βs : α}
    (hQ : ConstRun q Tq Q.a Q.b αs) (hK : ConstRun k Tk Q.c Q.d βs)
    (hne : αs ≠ βs) :
    ∀ t, queryTemplateField Q q k Tq Tk t = queryActualField Q q k Tq Tk t := by
  intro t
  cases hq : Q.isQ
  · simpa [queryTemplateField, queryActualField, queryTemplates,
      Query.bridges, hq, templateField, actualField, kOwnerTemplates] using
      (kOwnerTemplates_max_eq_actual
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := Q.a) (b := Q.b) (c := Q.c) (d := Q.d) (u := Q.owner)
        (αs := αs) (βs := βs) hQ hK hne t)
  · simpa [queryTemplateField, queryActualField, queryTemplates,
      Query.bridges, hq, templateField, actualField, qOwnerTemplates] using
      (qOwnerTemplates_max_eq_actual
        (q := q) (k := k) (Tq := Tq) (Tk := Tk)
        (a := Q.a) (b := Q.b) (c := Q.c) (d := Q.d) (p := Q.owner)
        (αs := αs) (βs := βs) hQ hK hne t)

/-- Headline form of the corrected `runPairTemplates` equivalence. -/
theorem runPairTemplates_corrected_max_eq_actual {Q : Query} {q k : Nat → α}
    {Tq Tk : Nat} {αs βs : α}
    (hQ : ConstRun q Tq Q.a Q.b αs) (hK : ConstRun k Tk Q.c Q.d βs)
    (hne : αs ≠ βs) :
    ∀ t, templateField (runPairOwnerTemplates Q q k Tq Tk) t =
      queryActualField Q q k Tq Tk t := by
  intro t
  exact queryTemplates_max_eq_actual hQ hK hne t

/-- Strict-interior Q-owner template size bound. -/
theorem qOwnerTemplates_length_le_three {q k : Nat → α}
    {Tq Tk a b c d p : Nat} (hap : a < p) (hpb : p < b) :
    (qOwnerTemplates q k Tq Tk a b c d p).length ≤ 3 := by
  simpa [qOwnerTemplates] using
    (qOwnerCompressed_length_le_three (q := q) (k := k)
      (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := c) (d := d)
      (p := p) hap hpb)

/-- Strict-interior K-owner template size bound. -/
theorem kOwnerTemplates_length_le_three {q k : Nat → α}
    {Tq Tk a b c d u : Nat} (hcu : c < u) (hud : u < d) :
    (kOwnerTemplates q k Tq Tk a b c d u).length ≤ 3 := by
  simpa [kOwnerTemplates] using
    (kOwnerCompressed_length_le_three (q := q) (k := k)
      (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := c) (d := d)
      (u := u) hcu hud)

/-! ### The explicit three-slot forms -/

/-- Q-side explicit template field: the two K-edge slots and the interior bulk
delegate `u_*`. -/
def qOwnerThreeField (q k : Nat → α) (Tq Tk a b c d p : Nat) (t : Nat) : Route :=
  rmax (qSlot q k Tq Tk a b c d p c t)
    (rmax (qSlot q k Tq Tk a b c d p d t)
      (qSlot q k Tq Tk a b c d p (min (d - 1) (p - 1)) t))

/-- K-side explicit template field: the interior bulk plus the two Q-edge slots. -/
def kOwnerThreeField (q k : Nat → α) (Tq Tk a b c d u : Nat) (t : Nat) : Route :=
  rmax (OwnerCorrectK.bulkRoute a b u t)
    (rmax (kSlot q k Tq Tk a b c d u a t)
      (kSlot q k Tq Tk a b c d u b t))

/-- For a strict-interior Q-owner, the exact template field has the three
explicit slots `c`, `d`, and `min (d-1) (p-1)`. -/
theorem qOwnerThreeField_eq_actual {q k : Nat → α}
    {Tq Tk a b c d p : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hap : a < p) (hpb : p < b) :
    ∀ t, qOwnerThreeField q k Tq Tk a b c d p t =
      actualField (OwnerBridges.qOwnerBridges q k Tq Tk a b c d p) t := by
  intro t
  calc
    qOwnerThreeField q k Tq Tk a b c d p t
        = templateField (qOwnerTemplates q k Tq Tk a b c d p) t := by
          simpa [qOwnerThreeField, qOwnerTemplates, templateField] using
            (qOwner_field_three (q := q) (k := k)
              (Tq := Tq) (Tk := Tk) (a := a) (b := b)
              (c := c) (d := d) (p := p) hap hpb t).symm
    _ = actualField (OwnerBridges.qOwnerBridges q k Tq Tk a b c d p) t :=
      qOwnerTemplates_max_eq_actual hQ hK hne t

/-- For a strict-interior K-owner, the exact template field has the three
explicit slots: bulk `(u)` plus the Q-edge centres `a`, `b`. -/
theorem kOwnerThreeField_eq_actual {q k : Nat → α}
    {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hcu : c < u) (hud : u < d) :
    ∀ t, kOwnerThreeField q k Tq Tk a b c d u t =
      actualField (OwnerBridges.kOwnerBridges q k Tq Tk a b c d u) t := by
  intro t
  calc
    kOwnerThreeField q k Tq Tk a b c d u t
        = templateField (kOwnerTemplates q k Tq Tk a b c d u) t := by
          simpa [kOwnerThreeField, kOwnerTemplates, templateField] using
            (kOwner_field_three (q := q) (k := k)
              (Tq := Tq) (Tk := Tk) (a := a) (b := b)
              (c := c) (d := d) (u := u) hcu hud t).symm
    _ = actualField (OwnerBridges.kOwnerBridges q k Tq Tk a b c d u) t :=
      kOwnerTemplates_max_eq_actual hQ hK hne t

end OwnerTemplateEquivalence

import OwnerKBaselineEnvelope
import QBridge
import QCut
import HookCut
import KDeleteEquivalence
import PayloadRouteAdapter

/-!
## Fixed-owner M3 cut+repair effective envelopes

This file is the final fixed-owner M3 adapter.  It keeps two route layers
separate:

* a **cut** route (`QCut.bruteQCut` on the Q side and
  `(rosaKDelete q k u).best` on the K side);
* a **repair** route, the actual active bridge maximum
  `OwnerTemplateEquivalence.actualField`.

For each fixed owner the effective route is the pointwise ROSA maximum of the
cut and repair layers.  The strict-interior three-slot templates and the
boundary literal bridge-candidate lists are both shown to express that same
effective route.

Owners are deliberately scoped: a fixed Q-owner only compares bridges with
`b.p = p`, and a fixed K-owner only compares bridges with `b.u = u`.  No
cross-owner route maximum is formed.  Consequently this file makes no
unconditional global no-reentry claim: the existing global theorem still
requires the explicit `CrossBlockIdentityIntervals` obligation.
-/

namespace EffectiveOwnerM3

open Route Lcs RunRect RosBridge OwnerBridges OwnerCompress OwnerTemplateEquivalence
open BridgeEnvelope KDeleteAbstract KDeleteROSA KDeleteEquivalence

variable {α : Type} [DecidableEq α]

/-! ### Generic cut/repair phase semantics -/

/-- The route-level effective phase: cut and repair, with repair selected when
it reaches the cut. -/
def cutRepairRoute (cut repair : Route) : Route :=
  rmax cut repair

/-- If the cut is below the repair route, the repair route wins exactly. -/
theorem cutRepairRoute_eq_repair_of_cut_rle {cut repair : Route}
    (h : rle cut repair) :
    cutRepairRoute cut repair = repair := by
  simp [cutRepairRoute, rmax, h]

/-- If the cut is not below the repair route, the cut wins exactly. -/
theorem cutRepairRoute_eq_cut_of_not_cut_rle {cut repair : Route}
    (h : ¬ rle cut repair) :
    cutRepairRoute cut repair = cut := by
  simp [cutRepairRoute, rmax, h]

/-- Exact two-way phase statement: either repair attains the effective route,
or the cut does because repair is strictly below it. -/
theorem cutRepairRoute_repair_or_cut (cut repair : Route) :
    (rle cut repair ∧ cutRepairRoute cut repair = repair) ∨
      (¬ rle cut repair ∧ cutRepairRoute cut repair = cut) := by
  by_cases h : rle cut repair
  · exact Or.inl ⟨h, cutRepairRoute_eq_repair_of_cut_rle h⟩
  · exact Or.inr ⟨h, cutRepairRoute_eq_cut_of_not_cut_rle h⟩

/-! ### Fixed Q-owner effective route -/

/-- Fixed Q-owner repair route: the maximum active bridge born at `p`. -/
def qRepairRoute (q k : Nat → α) (Tq Tk a b c d p : Nat) (t : Nat) : Route :=
  OwnerTemplateEquivalence.actualField
    (qOwnerBridges q k Tq Tk a b c d p) t

/-- Fixed Q-owner effective route: Q-cut maximum with the Q repair field. -/
def qEffectiveRoute (ell : Nat → Int) (q k : Nat → α)
    (Tq Tk a b c d p : Nat) (t : Nat) : Route :=
  cutRepairRoute (QCut.bruteQCut ell t p)
    (qRepairRoute q k Tq Tk a b c d p t)

/-- Closed-form Q-cut presentation of the Q effective route.  The hypotheses are
exactly the Q-cut closed-form domain. -/
theorem qEffectiveRoute_eq_qcutClosed (ell : Nat → Int) (q k : Nat → α)
    (Tq Tk a b c d p t : Nat) (hp : p ≤ t)
    (hnn : ∀ e, e < t → -1 ≤ ell e) :
    qEffectiveRoute ell q k Tq Tk a b c d p t =
      cutRepairRoute (QCut.qcutClosed ell t p)
        (qRepairRoute q k Tq Tk a b c d p t) := by
  unfold qEffectiveRoute
  rw [QCut.qcut_length_and_latest_endpoint ell t p hp hnn]

/-- Repair wins exactly when it reaches the cut route. -/
theorem qEffectiveRoute_eq_repair_iff_cut_rle (ell : Nat → Int) (q k : Nat → α)
    (Tq Tk a b c d p t : Nat) :
    qEffectiveRoute ell q k Tq Tk a b c d p t =
        qRepairRoute q k Tq Tk a b c d p t ↔
      rle (QCut.bruteQCut ell t p)
        (qRepairRoute q k Tq Tk a b c d p t) := by
  constructor
  · intro h
    let cut := QCut.bruteQCut ell t p
    let repair := qRepairRoute q k Tq Tk a b c d p t
    have h' : cutRepairRoute cut repair = repair := by
      simpa [qEffectiveRoute, cut, repair] using h
    have hle : rle cut repair := by
      have hleft := rle_rmax_left cut repair
      change rle cut (cutRepairRoute cut repair) at hleft
      rw [h'] at hleft
      exact hleft
    simpa [cut, repair] using hle
  · intro h
    change cutRepairRoute (QCut.bruteQCut ell t p)
      (qRepairRoute q k Tq Tk a b c d p t) =
      qRepairRoute q k Tq Tk a b c d p t
    exact cutRepairRoute_eq_repair_of_cut_rle h

/-- If repair is strictly below the cut, the effective Q route is literally the
cut route. -/
theorem qEffectiveRoute_eq_cut_of_repair_lt (ell : Nat → Int) (q k : Nat → α)
    (Tq Tk a b c d p t : Nat)
    (h : ¬ rle (QCut.bruteQCut ell t p)
      (qRepairRoute q k Tq Tk a b c d p t)) :
    qEffectiveRoute ell q k Tq Tk a b c d p t =
      QCut.bruteQCut ell t p := by
  change cutRepairRoute (QCut.bruteQCut ell t p)
    (qRepairRoute q k Tq Tk a b c d p t) = QCut.bruteQCut ell t p
  exact cutRepairRoute_eq_cut_of_not_cut_rle h

/-- The exact Q-side case split: either repair reaches the cut and is the
effective route, or it is strictly below the cut and the cut is the effective
route. -/
theorem qEffectiveRoute_repair_or_cut (ell : Nat → Int) (q k : Nat → α)
    (Tq Tk a b c d p t : Nat) :
    (rle (QCut.bruteQCut ell t p)
        (qRepairRoute q k Tq Tk a b c d p t) ∧
      qEffectiveRoute ell q k Tq Tk a b c d p t =
        qRepairRoute q k Tq Tk a b c d p t) ∨
    (¬ rle (QCut.bruteQCut ell t p)
        (qRepairRoute q k Tq Tk a b c d p t) ∧
      qEffectiveRoute ell q k Tq Tk a b c d p t =
        QCut.bruteQCut ell t p) := by
  let cut := QCut.bruteQCut ell t p
  let repair := qRepairRoute q k Tq Tk a b c d p t
  have h := cutRepairRoute_repair_or_cut cut repair
  simpa [qEffectiveRoute, cut, repair] using h

/-- An active bridge attaining the raw repair field also attains the Q effective
route.  This is the exact "repair wins" case. -/
theorem qEffectiveRoute_eq_bridge_iff_rawWinner_and_cut_rle
    (ell : Nat → Int) {q k : Nat → α} {Tq Tk a b c d p : Nat}
    {x : Bridge} {t : Nat}
    (hmem : x ∈ qOwnerBridges q k Tq Tk a b c d p) (hactive : x.Active t) :
    qEffectiveRoute ell q k Tq Tk a b c d p t = x.routeAt t ↔
      BridgeWins (qOwnerBridges q k Tq Tk a b c d p) x t ∧
        rle (QCut.bruteQCut ell t p) (x.routeAt t) := by
  constructor
  · intro h
    let cut := QCut.bruteQCut ell t p
    let repair := qRepairRoute q k Tq Tk a b c d p t
    have h' : cutRepairRoute cut repair = x.routeAt t := by
      simpa [qEffectiveRoute, cut, repair] using h
    have hcut : rle cut (x.routeAt t) := by
      have hle := rle_rmax_left cut repair
      change rle cut (cutRepairRoute cut repair) at hle
      rw [h'] at hle
      exact hle
    have hrep : rle repair (x.routeAt t) := by
      have hle := rle_rmax_right cut repair
      change rle repair (cutRepairRoute cut repair) at hle
      rw [h'] at hle
      exact hle
    have hxle : rle (x.routeAt t)
        (qRepairRoute q k Tq Tk a b c d p t) := by
      have hle := OwnerCorrect.rle_fieldBridges_of_mem hmem t
      simpa [qRepairRoute, OwnerTemplateEquivalence.actualField,
        OwnerCorrect.bval, hactive] using hle
    have hraw : qRepairRoute q k Tq Tk a b c d p t = x.routeAt t :=
      rle_antisymm _ _ hrep hxle
    have hxfield : x.routeAt t =
        OwnerCompress.fieldBridges (qOwnerBridges q k Tq Tk a b c d p) t := by
      simpa [qRepairRoute, OwnerTemplateEquivalence.actualField] using hraw.symm
    exact ⟨(BridgeEnvelope.route_eq_fieldBridges_iff_bridgeWins hmem hactive).mp hxfield,
      hcut⟩
  · rintro ⟨hwin, hcut⟩
    have hraw : qRepairRoute q k Tq Tk a b c d p t = x.routeAt t := by
      have hfield := BridgeEnvelope.bridgeWins_route_eq_fieldBridges hwin
      simpa [qRepairRoute, OwnerTemplateEquivalence.actualField] using hfield.symm
    change cutRepairRoute (QCut.bruteQCut ell t p)
      (qRepairRoute q k Tq Tk a b c d p t) = x.routeAt t
    rw [hraw]
    exact cutRepairRoute_eq_repair_of_cut_rle hcut

/-- Every raw Q repair winner wins the effective Q route: an active Q bridge
born at the fixed owner always beats the Q cut. -/
theorem qEffectiveRoute_eq_bridge_of_rawWinner
    (ell : Nat → Int) {q k : Nat → α} {Tq Tk a b c d p : Nat}
    {x : Bridge} {t : Nat}
    (hwin : BridgeWins (qOwnerBridges q k Tq Tk a b c d p) x t) :
    qEffectiveRoute ell q k Tq Tk a b c d p t = x.routeAt t := by
  have hp : x.p = p := qOwnerBridges_birth hwin.1
  have hcut := QBridge.q_bridge_beats_cut ell x p t hp hwin.2.1
  exact (qEffectiveRoute_eq_bridge_iff_rawWinner_and_cut_rle ell hwin.1 hwin.2.1).mpr
    ⟨hwin, hcut⟩

/-! ### Q strict-interior and boundary interfaces -/

/-- Strict-interior Q-owner effective route in explicit three-slot form. -/
theorem qEffectiveRoute_eq_threeField_of_strict
    (ell : Nat → Int) {q k : Nat → α} {Tq Tk a b c d p : Nat}
    {αs βs : α} (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hap : a < p) (hpb : p < b) (t : Nat) :
    qEffectiveRoute ell q k Tq Tk a b c d p t =
      cutRepairRoute (QCut.bruteQCut ell t p)
        (qOwnerThreeField q k Tq Tk a b c d p t) := by
  have hrep : qRepairRoute q k Tq Tk a b c d p t =
      qOwnerThreeField q k Tq Tk a b c d p t := by
    unfold qRepairRoute OwnerTemplateEquivalence.actualField
    exact (qOwnerThreeField_eq_actual (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d) (p := p)
      (αs := αs) (βs := βs) hQ hK hne hap hpb t).symm
  unfold qEffectiveRoute
  rw [hrep]

/-- At a Q boundary the compressed template list is the literal bridge list. -/
theorem qOwnerTemplates_eq_actual_candidates_of_boundary
    (q k : Nat → α) (Tq Tk a b c d p : Nat)
    (hboundary : ¬ (a < p ∧ p < b)) :
    qOwnerTemplates q k Tq Tk a b c d p =
      OwnerCompress.candsOf (qOwnerBridges q k Tq Tk a b c d p) := by
  have hfilter : (qOwnerBridges q k Tq Tk a b c d p).filter
        (OwnerCompress.qOwnerKept a b c d p) =
      qOwnerBridges q k Tq Tk a b c d p := by
    apply List.filter_eq_self.mpr
    intro x hx
    rw [OwnerCompress.qOwnerKept_eq]
    intro hcore
    exact hboundary ⟨hcore.1, hcore.2.1⟩
  simp [qOwnerTemplates, OwnerCompress.qOwnerCompressed,
    OwnerCompress.candsOf, hfilter]

/-- A boundary Q-owner effective route uses the literal actual-candidate list. -/
theorem qEffectiveRoute_boundary_eq_actual_candidates
    (ell : Nat → Int) (q k : Nat → α) (Tq Tk a b c d p t : Nat)
    (_hboundary : ¬ (a < p ∧ p < b)) :
    qEffectiveRoute ell q k Tq Tk a b c d p t =
      cutRepairRoute (QCut.bruteQCut ell t p)
        (OwnerCompress.field
          (OwnerCompress.candsOf (qOwnerBridges q k Tq Tk a b c d p)) t) := by
  unfold qEffectiveRoute qRepairRoute OwnerTemplateEquivalence.actualField
  rw [← OwnerCorrect.field_candsOf (qOwnerBridges q k Tq Tk a b c d p) t]

/-! ### Fixed K-owner effective route -/

/-- Fixed K-owner repair route: the maximum active bridge with K-owner `u`. -/
def kRepairRoute (q k : Nat → α) (Tq Tk a b c d u : Nat) (t : Nat) : Route :=
  OwnerTemplateEquivalence.actualField
    (kOwnerBridges q k Tq Tk a b c d u) t

/-- Fixed K-owner cut/deletion route: the exact ROSA delete-`k[u]` baseline. -/
def kCutRoute (q k : Nat → α) (u : Nat) (t : Nat) : Route :=
  (rosaKDelete q k u).best t

/-- Fixed K-owner effective route: `rosaKDelete.best` maximum with repair. -/
def kEffectiveRoute (q k : Nat → α) (Tq Tk a b c d u : Nat) (t : Nat) : Route :=
  cutRepairRoute (kCutRoute q k u t) (kRepairRoute q k Tq Tk a b c d u t)

/-- The same effective route is the existing raw-template/deletion envelope. -/
theorem kEffectiveRoute_eq_deletionAwareKOwnerEnvelope
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (t : Nat) :
    kEffectiveRoute q k Tq Tk a b c d u t =
      OwnerKBaselineEnvelope.deletionAwareKOwnerEnvelope q k Tq Tk a b c d u t := by
  let actual := OwnerTemplateEquivalence.actualField
    (kOwnerBridges q k Tq Tk a b c d u) t
  let raw := OwnerKBaselineEnvelope.rawKOwnerField q k Tq Tk a b c d u t
  have hraw : actual = raw := by
    change OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t = raw
    exact (OwnerKBaselineEnvelope.rawKOwnerTemplates_max_eq_actual
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d) (u := u)
      (αs := αs) (βs := βs) hQ hK hne t).symm
  change rmax ((rosaKDelete q k u).best t) actual =
    rmax raw ((rosaKDelete q k u).best t)
  rw [hraw]
  exact rmax_comm _ _

/-- K-side max semantics explicitly over `rosaKDelete.best` and the raw field. -/
theorem kEffectiveRoute_eq_rmax_rosa_best_raw
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (t : Nat) :
    kEffectiveRoute q k Tq Tk a b c d u t =
      rmax ((rosaKDelete q k u).best t)
        (OwnerKBaselineEnvelope.rawKOwnerField q k Tq Tk a b c d u t) := by
  let actual := OwnerTemplateEquivalence.actualField
    (kOwnerBridges q k Tq Tk a b c d u) t
  let raw := OwnerKBaselineEnvelope.rawKOwnerField q k Tq Tk a b c d u t
  have hraw : actual = raw := by
    change OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t = raw
    exact (OwnerKBaselineEnvelope.rawKOwnerTemplates_max_eq_actual
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d) (u := u)
      (αs := αs) (βs := βs) hQ hK hne t).symm
  change rmax ((rosaKDelete q k u).best t) actual =
    rmax ((rosaKDelete q k u).best t) raw
  rw [hraw]

/-- Hook-envelope presentation of the K cut layer. -/
theorem kEffectiveRoute_eq_rmax_hookCut_raw
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (t : Nat) :
    kEffectiveRoute q k Tq Tk a b c d u t =
      rmax (HookCut.hookCut (KDeleteEquivalence.lcsRow q k t) t u)
        (OwnerKBaselineEnvelope.rawKOwnerField q k Tq Tk a b c d u t) := by
  rw [kEffectiveRoute_eq_rmax_rosa_best_raw hQ hK hne t,
    KDeleteEquivalence.rosaKDelete_best_eq_hookCut q k u t]

/-- The exact K-side case split over the ROSA deletion baseline. -/
theorem kEffectiveRoute_repair_or_cut (q k : Nat → α)
    (Tq Tk a b c d u t : Nat) :
    (rle ((rosaKDelete q k u).best t)
        (kRepairRoute q k Tq Tk a b c d u t) ∧
      kEffectiveRoute q k Tq Tk a b c d u t =
        kRepairRoute q k Tq Tk a b c d u t) ∨
    (¬ rle ((rosaKDelete q k u).best t)
        (kRepairRoute q k Tq Tk a b c d u t) ∧
      kEffectiveRoute q k Tq Tk a b c d u t =
        (rosaKDelete q k u).best t) := by
  let cut := kCutRoute q k u t
  let repair := kRepairRoute q k Tq Tk a b c d u t
  have h := cutRepairRoute_repair_or_cut cut repair
  simpa [kEffectiveRoute, kCutRoute, cut, repair] using h

/-- A bridge attains the K effective route exactly when it is a raw repair
winner and beats the ROSA deletion baseline. -/
theorem kEffectiveRoute_eq_bridge_iff_rawWinner_and_beats
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {x : Bridge} {t : Nat}
    (hmem : x ∈ kOwnerBridges q k Tq Tk a b c d u)
    (hu : x.u = u) (hactive : x.Active t) :
    kEffectiveRoute q k Tq Tk a b c d u t = x.routeAt t ↔
      BridgeWins (kOwnerBridges q k Tq Tk a b c d u) x t ∧
        x.u = u ∧ (rosaKDelete q k u).Beats x t := by
  constructor
  · intro h
    let cut := kCutRoute q k u t
    let repair := kRepairRoute q k Tq Tk a b c d u t
    have h' : cutRepairRoute cut repair = x.routeAt t := by
      simpa [kEffectiveRoute, cut, repair] using h
    have hbest : rle cut (x.routeAt t) := by
      have hle := rle_rmax_left cut repair
      change rle cut (cutRepairRoute cut repair) at hle
      rw [h'] at hle
      exact hle
    have hrep : rle repair (x.routeAt t) := by
      have hle := rle_rmax_right cut repair
      change rle repair (cutRepairRoute cut repair) at hle
      rw [h'] at hle
      exact hle
    have hrep_field : repair =
        OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t := by
      dsimp [repair, kRepairRoute, OwnerTemplateEquivalence.actualField]
    have hxle : rle (x.routeAt t) repair := by
      have hle := OwnerCorrect.rle_fieldBridges_of_mem hmem t
      have hle' : rle (x.routeAt t)
          (OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t) := by
        simpa [OwnerCorrect.bval, hactive] using hle
      simpa [hrep_field] using hle'
    have hraw : repair = x.routeAt t := rle_antisymm _ _ hrep hxle
    have hxfield : x.routeAt t =
        OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t :=
      hraw.symm.trans hrep_field
    refine ⟨(BridgeEnvelope.route_eq_fieldBridges_iff_bridgeWins hmem hactive).mp hxfield,
      hu, ?_⟩
    exact (KDeleteEquivalence.beats_iff_best_rle (rosaKDelete q k u) x t hactive).mpr
      (by simpa [kCutRoute, cut] using hbest)
  · rintro ⟨hwin, _hu, hbeats⟩
    have hraw : kRepairRoute q k Tq Tk a b c d u t = x.routeAt t := by
      have hfield := BridgeEnvelope.bridgeWins_route_eq_fieldBridges hwin
      simpa [kRepairRoute, OwnerTemplateEquivalence.actualField] using hfield.symm
    have hbest : rle (kCutRoute q k u t) (x.routeAt t) := by
      simpa [kCutRoute] using
        (KDeleteEquivalence.beats_iff_best_rle (rosaKDelete q k u) x t hactive).mp hbeats
    change cutRepairRoute (kCutRoute q k u t)
      (kRepairRoute q k Tq Tk a b c d u t) = x.routeAt t
    rw [hraw]
    exact cutRepairRoute_eq_repair_of_cut_rle hbest

/-! ### K strict-interior and boundary interfaces -/

/-- Strict-interior K-owner effective route in explicit three-slot form. -/
theorem kEffectiveRoute_eq_threeField_of_strict
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hcu : c < u) (hud : u < d) (t : Nat) :
    kEffectiveRoute q k Tq Tk a b c d u t =
      cutRepairRoute ((rosaKDelete q k u).best t)
        (kOwnerThreeField q k Tq Tk a b c d u t) := by
  have hrep : kRepairRoute q k Tq Tk a b c d u t =
      kOwnerThreeField q k Tq Tk a b c d u t := by
    unfold kRepairRoute OwnerTemplateEquivalence.actualField
    rw [← OwnerKBaselineEnvelope.rawKOwnerTemplates_max_eq_actual
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d) (u := u)
      (αs := αs) (βs := βs) hQ hK hne t]
    exact OwnerKBaselineEnvelope.rawKOwnerField_eq_threeField_of_strict
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d) (u := u)
      (αs := αs) (βs := βs) hQ hK hne hcu hud t
  unfold kEffectiveRoute kCutRoute
  rw [hrep]

/-- At a K boundary the compressed template list is the literal bridge list. -/
theorem kOwnerTemplates_eq_actual_candidates_of_boundary
    (q k : Nat → α) (Tq Tk a b c d u : Nat)
    (hboundary : ¬ (c < u ∧ u < d)) :
    kOwnerTemplates q k Tq Tk a b c d u =
      OwnerCompress.candsOf (kOwnerBridges q k Tq Tk a b c d u) :=
  OwnerKBaselineEnvelope.rawKOwnerTemplates_eq_actual_candidates_of_boundary
    q k Tq Tk a b c d u hboundary

/-- A boundary K-owner effective route uses the literal actual-candidate list. -/
theorem kEffectiveRoute_boundary_eq_actual_candidates
    (q k : Nat → α) (Tq Tk a b c d u t : Nat)
    (_hboundary : ¬ (c < u ∧ u < d)) :
    kEffectiveRoute q k Tq Tk a b c d u t =
      cutRepairRoute ((rosaKDelete q k u).best t)
        (OwnerCompress.field
          (OwnerCompress.candsOf (kOwnerBridges q k Tq Tk a b c d u)) t) := by
  unfold kEffectiveRoute kCutRoute kRepairRoute OwnerTemplateEquivalence.actualField
  rw [← OwnerCorrect.field_candsOf (kOwnerBridges q k Tq Tk a b c d u) t]

/-! ### Owner scoping: cross-owner candidates do not compete -/

/-- Every member of a fixed Q-owner repair collection has the same Q-owner. -/
def QOwnerScoped (p : Nat) (bs : List Bridge) : Prop :=
  ∀ b ∈ bs, b.p = p

/-- Every member of a fixed K-owner repair collection has the same K-owner. -/
def KOwnerScoped (u : Nat) (bs : List Bridge) : Prop :=
  ∀ b ∈ bs, b.u = u

theorem qOwnerBridges_scoped (q k : Nat → α) (Tq Tk a b c d p : Nat) :
    QOwnerScoped p (qOwnerBridges q k Tq Tk a b c d p) := by
  intro x hx
  exact qOwnerBridges_birth hx

theorem kOwnerBridges_scoped (q k : Nat → α) (Tq Tk a b c d u : Nat) :
    KOwnerScoped u (kOwnerBridges q k Tq Tk a b c d u) := by
  intro x hx
  exact kOwnerBridges_u hx

/-- A bridge with a different Q-owner is absent from this owner's repair list. -/
theorem qOwnerBridges_excludes_cross_owner
    {q k : Nat → α} {Tq Tk a b c d p : Nat} {x : Bridge}
    (howner : x.p ≠ p) :
    x ∉ qOwnerBridges q k Tq Tk a b c d p := by
  intro hx
  exact howner (qOwnerBridges_birth hx)

/-- A bridge with a different K-owner is absent from this owner's repair list. -/
theorem kOwnerBridges_excludes_cross_owner
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {x : Bridge}
    (howner : x.u ≠ u) :
    x ∉ kOwnerBridges q k Tq Tk a b c d u := by
  intro hx
  exact howner (kOwnerBridges_u hx)

/-- Any global segment bound must carry the explicit cross-block interval
obligation.  This wrapper is the only global no-re-entry-facing statement here;
there is no unconditional global claim. -/
theorem global_segments_le_three_mul_with_explicit_crossBlock
    {T : Nat} (blocks : List (List Bridge))
    (hlen : ∀ bl ∈ blocks, bl.length ≤ 3)
    (hcross : OwnerKBaselineEnvelope.CrossBlockIdentityIntervals blocks)
    (hcover : ∀ t, t < T →
      ∃ b ∈ blocks.flatten,
        BlockWinnerNoReentry.globalLocalWins blocks.flatten b t) :
    ((List.range T).filter (fun t =>
      decide (Phase12b.IsSegStart
        (BlockWinnerNoReentry.globalWinnerLabel blocks.flatten) t))).length ≤
      3 * blocks.length :=
  OwnerKBaselineEnvelope.global_segments_le_three_mul_of_crossBlockIdentityIntervals
    blocks hlen hcross hcover

/-- The fixed Q-owner and fixed K-owner effective routes are separate
owner-indexed objects; no Q/K cross-owner maximum is introduced. -/
theorem q_and_k_effective_routes_are_owner_scoped
    (q k : Nat → α) (Tq Tk a b c d p u : Nat) :
    QOwnerScoped p (qOwnerBridges q k Tq Tk a b c d p) ∧
      KOwnerScoped u (kOwnerBridges q k Tq Tk a b c d u) :=
  ⟨qOwnerBridges_scoped q k Tq Tk a b c d p,
    kOwnerBridges_scoped q k Tq Tk a b c d u⟩

end EffectiveOwnerM3

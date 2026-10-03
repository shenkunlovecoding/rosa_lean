import OwnerTemplateEquivalence
import BridgeEnvelope
import KDeleteEquivalence
import KDeleteROSA
import KSkyline
import BlockWinnerNoReentry
import WinnerPieces

/-!
## Fixed K-owner templates and the deletion-aware effective envelope

This file closes the missing adapter between the fixed-K-owner compressed
templates and the deletion-aware K winner.

There are two distinct route fields:

* the **raw** bridge field, obtained from `kOwnerBridges` or, equivalently, from
  `OwnerTemplateEquivalence.kOwnerTemplates`;
* the **deletion baseline** `(rosaKDelete q k u).best`.

The effective envelope is their pointwise `rmax`.  A bridge is an effective
winner exactly when it attains this envelope, which is equivalent to being both
a raw bridge winner and beating the deletion baseline.

For a strict-interior K-owner the raw field has the explicit three-slot form
`kOwnerThreeField`.  At a K-owner boundary the bulk slot disappears, and the raw
template list is exactly the literal `candsOf kOwnerBridges` list.  No `sorry` or
axiom is used.
-/

namespace OwnerKBaselineEnvelope

open Route RosBridge CommonBirth OwnerBridges OwnerCompress RunRect
open OwnerTemplateEquivalence BridgeEnvelope KDeleteAbstract KDeleteROSA
open KDeleteEquivalence BlockWinnerNoReentry

variable {α : Type} [DecidableEq α]

/-! ### Generic raw/deletion envelope -/

/-- The deletion-aware effective envelope: the pointwise maximum of the raw
bridge field and the deletion baseline.  This is the route-level meaning of
"raw bridge winner `max` `rosaKDelete.best`". -/
def effectiveWinnerEnvelope (D : KDeleteFamily) (bs : List Bridge)
    (t : Nat) : Route :=
  rmax (OwnerCompress.fieldBridges bs t) (D.best t)

/-- The deletion-aware effective K winner.  This is definitionally the existing
fixed-owner baseline-aware winner; the envelope characterization below makes the
raw/deletion split explicit. -/
abbrev EffectiveKWinner (D : KDeleteFamily) (u : Nat) (bs : List Bridge)
    (b : Bridge) (t : Nat) : Prop :=
  BridgeEnvelope.KBaselineWinner D u bs b t

/-- A bridge attains the effective envelope exactly when it is a raw bridge
winner and beats the deletion baseline. -/
theorem effectiveWinnerEnvelope_eq_route_iff_rawWinner_and_beats
    {D : KDeleteFamily} {bs : List Bridge} {b : Bridge} {t : Nat}
    (hmem : b ∈ bs) (hactive : b.Active t) :
    effectiveWinnerEnvelope D bs t = b.routeAt t ↔
      BridgeWins bs b t ∧ D.Beats b t := by
  constructor
  · intro h
    have hraw_eq : rmax (OwnerCompress.fieldBridges bs t) (D.best t) =
        b.routeAt t := by
      simpa [effectiveWinnerEnvelope] using h
    have hb_le_raw : rle (b.routeAt t) (OwnerCompress.fieldBridges bs t) := by
      unfold OwnerCompress.fieldBridges
      apply rle_rmaxList
      rw [List.mem_map]
      exact ⟨b, hmem, by simp [hactive]⟩
    have hraw_le_b : rle (OwnerCompress.fieldBridges bs t) (b.routeAt t) := by
      have hle := rle_rmax_left (OwnerCompress.fieldBridges bs t) (D.best t)
      rw [hraw_eq] at hle
      exact hle
    have hraw : OwnerCompress.fieldBridges bs t = b.routeAt t :=
      rle_antisymm _ _ hraw_le_b hb_le_raw
    have hbw : BridgeWins bs b t :=
      (route_eq_fieldBridges_iff_bridgeWins hmem hactive).mp hraw.symm
    have hbest : rle (D.best t) (b.routeAt t) := by
      have hle := rle_rmax_right (OwnerCompress.fieldBridges bs t) (D.best t)
      rw [hraw_eq] at hle
      exact hle
    exact ⟨hbw, (beats_iff_best_rle D b t hactive).mpr hbest⟩
  · rintro ⟨hbw, hbeats⟩
    have hraw : OwnerCompress.fieldBridges bs t = b.routeAt t :=
      (bridgeWins_route_eq_fieldBridges hbw).symm
    have hbest : rle (D.best t) (b.routeAt t) :=
      (beats_iff_best_rle D b t hactive).mp hbeats
    unfold effectiveWinnerEnvelope
    apply rle_antisymm
    · apply (rle_rmax_lub (OwnerCompress.fieldBridges bs t) (D.best t)
          (b.routeAt t)).mpr
      exact ⟨by simpa [hraw] using rle_refl (b.routeAt t), hbest⟩
    · rw [hraw]
      exact rle_rmax_left _ _

/-- The effective winner admits the precise envelope characterization.  The
hypotheses identify the actual bridge; the fixed-owner/raw conditions are still
part of `EffectiveKWinner`. -/
theorem effectiveKWinner_iff_envelope_eq
    {D : KDeleteFamily} {u : Nat} {bs : List Bridge} {b : Bridge} {t : Nat}
    (hmem : b ∈ bs) (hu : b.u = u) (hactive : b.Active t) :
    EffectiveKWinner D u bs b t ↔
      effectiveWinnerEnvelope D bs t = b.routeAt t := by
  rw [EffectiveKWinner, BridgeEnvelope.kBaselineWinner_iff_rawWinner_and_beats]
  constructor
  · rintro ⟨hbw, _hu', hbeats⟩
    exact (effectiveWinnerEnvelope_eq_route_iff_rawWinner_and_beats hmem hactive).mpr
      ⟨hbw, hbeats⟩
  · intro h
    have hraw :=
      (effectiveWinnerEnvelope_eq_route_iff_rawWinner_and_beats hmem hactive).mp h
    exact ⟨hraw.1, hu, hraw.2⟩

/-- The effective winner is exactly a raw bridge winner that also beats the
deletion baseline.  This is the direct raw-winner/`D.Beats` interface. -/
theorem effectiveKWinner_iff_rawWinner_and_beats
    {D : KDeleteFamily} {u : Nat} {bs : List Bridge} {b : Bridge} {t : Nat}
    (hu : b.u = u) :
    EffectiveKWinner D u bs b t ↔ BridgeWins bs b t ∧ D.Beats b t := by
  rw [EffectiveKWinner, BridgeEnvelope.kBaselineWinner_iff_rawWinner_and_beats]
  constructor
  · rintro ⟨hbw, _hu', hbeats⟩
    exact ⟨hbw, hbeats⟩
  · rintro ⟨hbw, hbeats⟩
    exact ⟨hbw, hu, hbeats⟩

/-- Route-level `rmax` form of the effective winner condition. -/
theorem effectiveKWinner_iff_max_raw_and_delete
    {D : KDeleteFamily} {u : Nat} {bs : List Bridge} {b : Bridge} {t : Nat}
    (hmem : b ∈ bs) (hu : b.u = u) (hactive : b.Active t) :
    EffectiveKWinner D u bs b t ↔
      rmax (OwnerCompress.fieldBridges bs t) (D.best t) = b.routeAt t := by
  simpa [effectiveWinnerEnvelope] using
    (effectiveKWinner_iff_envelope_eq hmem hu hactive)

/-! ### Fixed K-owner raw templates -/

/-- The raw fixed-K-owner templates.  For a strict-interior K-owner this is the
bulk plus the two edge slots; at a boundary the bulk is absent. -/
def rawKOwnerTemplates (q k : Nat → α) (Tq Tk a b c d u : Nat) : List Cand :=
  OwnerTemplateEquivalence.kOwnerTemplates q k Tq Tk a b c d u

/-- The raw fixed-K-owner template field. -/
def rawKOwnerField (q k : Nat → α) (Tq Tk a b c d u : Nat) (t : Nat) : Route :=
  OwnerTemplateEquivalence.templateField
    (rawKOwnerTemplates q k Tq Tk a b c d u) t

/-- The deletion-aware fixed-K-owner envelope: raw templates `max` deletion
baseline. -/
def deletionAwareKOwnerEnvelope (q k : Nat → α) (Tq Tk a b c d u : Nat)
    (t : Nat) : Route :=
  rmax (rawKOwnerField q k Tq Tk a b c d u t)
    ((rosaKDelete q k u).best t)

/-- Raw templates reproduce the literal raw bridge field for every K-owner,
including boundary and out-of-range cases. -/
theorem rawKOwnerTemplates_max_eq_actual {q k : Nat → α}
    {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) :
    ∀ t, rawKOwnerField q k Tq Tk a b c d u t =
      OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t := by
  intro t
  simpa [rawKOwnerField, rawKOwnerTemplates,
    OwnerTemplateEquivalence.templateField, OwnerTemplateEquivalence.actualField]
    using OwnerTemplateEquivalence.kOwnerTemplates_max_eq_actual
      (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d) (u := u)
      (αs := αs) (βs := βs) hQ hK hne t

/-- The template/deletion envelope has exactly the generic raw/deletion
semantics. -/
theorem deletionAwareKOwnerEnvelope_eq_effectiveWinnerEnvelope
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (t : Nat) :
    deletionAwareKOwnerEnvelope q k Tq Tk a b c d u t =
      effectiveWinnerEnvelope (rosaKDelete q k u)
        (kOwnerBridges q k Tq Tk a b c d u) t := by
  unfold deletionAwareKOwnerEnvelope effectiveWinnerEnvelope
  rw [rawKOwnerTemplates_max_eq_actual (q := q) (k := k) (Tq := Tq) (Tk := Tk)
    (a := a) (b := b) (c := c) (d := d) (u := u)
    (αs := αs) (βs := βs) hQ hK hne t]

/-- Definitional raw/delete decomposition, named for downstream rewriting. -/
theorem deletionAwareKOwnerEnvelope_eq_rmax
    (q k : Nat → α) (Tq Tk a b c d u t : Nat) :
    deletionAwareKOwnerEnvelope q k Tq Tk a b c d u t =
      rmax (rawKOwnerField q k Tq Tk a b c d u t)
        ((rosaKDelete q k u).best t) := rfl

/-! ### Strict-interior three-slot form -/

/-- Strict-interior K-owner: the raw template field is exactly the explicit
three-slot field (bulk plus the two Q-edge slots). -/
theorem rawKOwnerField_eq_threeField_of_strict {q k : Nat → α}
    {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hcu : c < u) (hud : u < d) :
    ∀ t, rawKOwnerField q k Tq Tk a b c d u t =
      OwnerTemplateEquivalence.kOwnerThreeField q k Tq Tk a b c d u t := by
  intro t
  rw [rawKOwnerTemplates_max_eq_actual (q := q) (k := k) (Tq := Tq)
    (Tk := Tk) (a := a) (b := b) (c := c) (d := d) (u := u)
    (αs := αs) (βs := βs) hQ hK hne t]
  exact (OwnerTemplateEquivalence.kOwnerThreeField_eq_actual
    (q := q) (k := k) (Tq := Tq) (Tk := Tk) (a := a) (b := b)
    (c := c) (d := d) (u := u) (αs := αs) (βs := βs)
    hQ hK hne hcu hud t).symm

/-- Effective fixed-K-owner envelope in strict-interior form. -/
theorem deletionAwareKOwnerEnvelope_eq_threeField_of_strict
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hcu : c < u) (hud : u < d) (t : Nat) :
    deletionAwareKOwnerEnvelope q k Tq Tk a b c d u t =
      rmax (OwnerTemplateEquivalence.kOwnerThreeField q k Tq Tk a b c d u t)
        ((rosaKDelete q k u).best t) := by
  unfold deletionAwareKOwnerEnvelope
  rw [rawKOwnerField_eq_threeField_of_strict (q := q) (k := k) (Tq := Tq)
    (Tk := Tk) (a := a) (b := b) (c := c) (d := d) (u := u)
    (αs := αs) (βs := βs) hQ hK hne hcu hud t]

/-! ### K-owner boundary degeneration -/

/-- At a non-strict K-owner, the compressed raw template list is literally the
bridge-candidate list: there is no bulk compression. -/
theorem rawKOwnerTemplates_eq_actual_candidates_of_boundary
    (q k : Nat → α) (Tq Tk a b c d u : Nat)
    (hboundary : ¬ (c < u ∧ u < d)) :
    rawKOwnerTemplates q k Tq Tk a b c d u =
      OwnerCompress.candsOf (kOwnerBridges q k Tq Tk a b c d u) := by
  have hfilter : OwnerCompress.kOwnerKeptList q k Tq Tk a b c d u =
      kOwnerBridges q k Tq Tk a b c d u := by
    unfold OwnerCompress.kOwnerKeptList
    apply List.filter_eq_self.mpr
    intro x hx
    rw [OwnerCompress.kOwnerKept_eq]
    intro hcore
    exact hboundary ⟨hcore.2.2.1, hcore.2.2.2⟩
  simp [rawKOwnerTemplates, OwnerTemplateEquivalence.kOwnerTemplates,
    OwnerCompress.kOwnerCompressed, OwnerCompress.candsOf, hboundary, hfilter]

/-- Left-boundary specialization `u = c`. -/
theorem rawKOwnerTemplates_eq_actual_candidates_of_left_boundary
    (q k : Nat → α) (Tq Tk a b c d u : Nat) (hu : u = c) :
    rawKOwnerTemplates q k Tq Tk a b c d u =
      OwnerCompress.candsOf (kOwnerBridges q k Tq Tk a b c d u) := by
  apply rawKOwnerTemplates_eq_actual_candidates_of_boundary
  omega

/-- Right-boundary specialization `u = d`. -/
theorem rawKOwnerTemplates_eq_actual_candidates_of_right_boundary
    (q k : Nat → α) (Tq Tk a b c d u : Nat) (hu : u = d) :
    rawKOwnerTemplates q k Tq Tk a b c d u =
      OwnerCompress.candsOf (kOwnerBridges q k Tq Tk a b c d u) := by
  apply rawKOwnerTemplates_eq_actual_candidates_of_boundary
  omega

/-- Boundary fixed-K-owner envelope, with the bulk slot absent. -/
theorem deletionAwareKOwnerEnvelope_boundary_eq_actual
    {q k : Nat → α} {Tq Tk a b c d u : Nat}
    (hboundary : ¬ (c < u ∧ u < d)) (t : Nat) :
    deletionAwareKOwnerEnvelope q k Tq Tk a b c d u t =
      rmax (OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t)
        ((rosaKDelete q k u).best t) := by
  unfold deletionAwareKOwnerEnvelope rawKOwnerField
  rw [rawKOwnerTemplates_eq_actual_candidates_of_boundary
    (q := q) (k := k) (Tq := Tq) (Tk := Tk)
    (a := a) (b := b) (c := c) (d := d) (u := u) hboundary]
  change rmax (OwnerCompress.field
      (OwnerCompress.candsOf (kOwnerBridges q k Tq Tk a b c d u)) t)
      ((rosaKDelete q k u).best t) =
    rmax (OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t)
      ((rosaKDelete q k u).best t)
  rw [OwnerCorrect.field_candsOf]

/-- Strict-interior capstone: an effective K winner is exactly a bridge whose
route equals the raw three-slot template field and which beats the deletion
baseline. -/
theorem strictKOwner_effectiveWinner_iff_threeField_and_beats
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    {x : Bridge} {t : Nat}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hcu : c < u) (hud : u < d)
    (hmem : x ∈ kOwnerBridges q k Tq Tk a b c d u) (hu : x.u = u)
    (hactive : x.Active t) :
    EffectiveKWinner (rosaKDelete q k u) u (kOwnerBridges q k Tq Tk a b c d u) x t ↔
      x.routeAt t = OwnerTemplateEquivalence.kOwnerThreeField q k Tq Tk a b c d u t ∧
        (rosaKDelete q k u).Beats x t := by
  rw [effectiveKWinner_iff_rawWinner_and_beats hu]
  constructor
  · rintro ⟨hbw, hbeats⟩
    have hroute : x.routeAt t =
        OwnerTemplateEquivalence.kOwnerThreeField q k Tq Tk a b c d u t := by
      calc
        x.routeAt t = OwnerCompress.fieldBridges
            (kOwnerBridges q k Tq Tk a b c d u) t :=
          bridgeWins_route_eq_fieldBridges hbw
        _ = rawKOwnerField q k Tq Tk a b c d u t :=
          (rawKOwnerTemplates_max_eq_actual (q := q) (k := k)
            (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := c) (d := d)
            (u := u) (αs := αs) (βs := βs) hQ hK hne t).symm
        _ = OwnerTemplateEquivalence.kOwnerThreeField q k Tq Tk a b c d u t :=
          rawKOwnerField_eq_threeField_of_strict (q := q) (k := k)
            (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := c) (d := d)
            (u := u) (αs := αs) (βs := βs) hQ hK hne hcu hud t
    exact ⟨hroute, hbeats⟩
  · rintro ⟨hroute, hbeats⟩
    have hrouteRaw : x.routeAt t =
        OwnerCompress.fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t := by
      rw [← rawKOwnerTemplates_max_eq_actual (q := q) (k := k)
        (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := c) (d := d)
        (u := u) (αs := αs) (βs := βs) hQ hK hne t]
      rw [rawKOwnerField_eq_threeField_of_strict (q := q) (k := k)
        (Tq := Tq) (Tk := Tk) (a := a) (b := b) (c := c) (d := d)
        (u := u) (αs := αs) (βs := βs) hQ hK hne hcu hud t]
      exact hroute
    exact ⟨(route_eq_fieldBridges_iff_bridgeWins hmem hactive).mp hrouteRaw, hbeats⟩

/-! ### Deletion-aware interval and no-reentry consequences -/

/-- The concrete ROSA fixed-owner winner interval.  This is precisely the role
of the deletion baseline in the K-skyline: the winner cannot begin before
`d`, and then has no same-owner re-entry until the bridge expires. -/
theorem rosaKBaselineWinner_iff_window
    {q k : Nat → α} {u : Nat} {bs : List Bridge} {b : Bridge}
    (hreal : ∀ c ∈ bs, klexLT c.kappa b.kappa → RealisedK q k u c)
    (hreach : ∀ c ∈ bs, klexLT c.kappa b.kappa → c.shadowStart ≤ (b.p : Int))
    {d : Nat}
    (hdlow : ∀ t, b.p ≤ t → t < d → ¬ (rosaKDelete q k u).Beats b t)
    (hdhigh : ∀ t, d ≤ t → t ≤ b.death → (rosaKDelete q k u).Beats b t)
    {M : Nat}
    (hM : ∀ c ∈ bs, klexLT c.kappa b.kappa → c.death ≤ M)
    (hMat : M < b.p ∨ ∃ c ∈ bs, klexLT c.kappa b.kappa ∧ c.death = M)
    (t : Nat) :
    EffectiveKWinner (rosaKDelete q k u) u bs b t ↔
      b ∈ bs ∧ b.u = u ∧ max b.p (max d (M + 1)) ≤ t ∧ t ≤ b.death := by
  simpa [EffectiveKWinner, BridgeEnvelope.KBaselineWinner] using
    (BlockWinnerNoReentry.kLocalWins_rosa_iff
      (q := q) (k := k) (u := u) (bs := bs) (b := b)
      hreal hreach hdlow hdhigh hM hMat (t := t))

/-- One fixed K-owner bridge has no re-entry once its ROSA window is supplied. -/
theorem fixedKOwner_effectiveWinner_isInterval_of_window
    {q k : Nat → α} {u : Nat} {bs : List Bridge} {b : Bridge}
    (hwindow : HasRosaKWindow q k u bs b) :
    Phase12b.IsInterval
      (fun t => EffectiveKWinner (rosaKDelete q k u) u bs b t) := by
  simpa [EffectiveKWinner, BridgeEnvelope.KBaselineWinner] using
    (BlockWinnerNoReentry.kLocalWins_rosa_isInterval_of_window
      (q := q) (k := k) (u := u) (bs := bs) (b := b) hwindow)

/-- The canonical fixed-K-owner identity classes are intervals, hence cannot
re-enter within one owner, once every competitor bridge has its ROSA window. -/
theorem fixedKOwner_canonicalWinner_isInterval_of_windows
    {q k : Nat → α} {u : Nat} {bs : List Bridge} {κ : Int × Int}
    (hwindow : ∀ b ∈ bs, HasRosaKWindow q k u bs b) :
    Phase12b.IsInterval (fun t =>
      BlockWinnerNoReentry.kWinnerLabel (rosaKDelete q k u) u bs t = some κ) := by
  apply BlockWinnerNoReentry.kWinnerLabel_isInterval_some
  intro b hb
  exact fixedKOwner_effectiveWinner_isInterval_of_window
    (q := q) (k := k) (u := u) (bs := bs) (b := b) (hwindow b hb)

/-! ### The remaining external conditions -/

/-- The exact cross-block obligation left after the fixed-owner closure: every
canonical global winner label occurring in the blocks must have interval
preimage.  It is not implied by the local K theorem; the counterexample in
`BlockWinnerNoReentry` shows why. -/
def CrossBlockIdentityIntervals (blocks : List (List Bridge)) : Prop :=
  ∀ κ ∈ (BlockWinnerNoReentry.labelBlocks blocks).flatten,
    Phase12b.IsInterval (fun t =>
      BlockWinnerNoReentry.globalWinnerLabel blocks.flatten t = κ)

/-- Conditional global segment bound with the remaining cross-block condition
made explicit. -/
theorem global_segments_le_three_mul_of_crossBlockIdentityIntervals
    {T : Nat} (blocks : List (List Bridge))
    (hlen : ∀ bl ∈ blocks, bl.length ≤ 3)
    (hcross : CrossBlockIdentityIntervals blocks)
    (hcover : ∀ t, t < T →
      ∃ b ∈ blocks.flatten, BlockWinnerNoReentry.globalLocalWins blocks.flatten b t) :
    ((List.range T).filter (fun t =>
      decide (Phase12b.IsSegStart
        (BlockWinnerNoReentry.globalWinnerLabel blocks.flatten) t))).length ≤
      3 * blocks.length := by
  exact BlockWinnerNoReentry.global_segments_le_three_mul blocks hlen hcross hcover

/-- A fixed owner is shared by every bridge in a bridge list.  This is the
owner-separation hypothesis needed before a multi-block K bound can be reduced
to the fixed-owner theorem. -/
def OwnerUniform (u : Nat) (bs : List Bridge) : Prop :=
  ∀ b ∈ bs, b.u = u

/-- A single-owner K block bound.  `OwnerUniform` is the explicit
owner-separation requirement; `hwindow` remains the ROSA/deletion-window
obligation. -/
theorem kOwner_segments_le_three_mul_of_uniform
    {q k : Nat → α} {u T : Nat} (blocks : List (List Bridge))
    (howner : OwnerUniform u blocks.flatten)
    (hlen : ∀ bl ∈ blocks, bl.length ≤ 3)
    (hwindow : ∀ b ∈ blocks.flatten, HasRosaKWindow q k u blocks.flatten b)
    (hcover : ∀ t, t < T →
      ∃ b ∈ blocks.flatten, BridgeWins blocks.flatten b t ∧
        (rosaKDelete q k u).Beats b t) :
    ((List.range T).filter (fun t => decide
      (Phase12b.IsSegStart
        (BlockWinnerNoReentry.kWinnerLabel
          (rosaKDelete q k u) u blocks.flatten) t))).length ≤
      3 * blocks.length := by
  apply BlockWinnerNoReentry.k_segments_le_three_mul
    (q := q) (k := k) (u := u) (blocks := blocks) hlen hwindow
  intro t ht
  obtain ⟨b, hb, hbw, hbeats⟩ := hcover t ht
  have hu : b.u = u := howner b hb
  have hwin : EffectiveKWinner (rosaKDelete q k u) u blocks.flatten b t :=
    (effectiveKWinner_iff_rawWinner_and_beats (D := rosaKDelete q k u) hu).mpr
      ⟨hbw, hbeats⟩
  exact ⟨b, hb, by simpa [EffectiveKWinner, BridgeEnvelope.KBaselineWinner] using hwin⟩

end OwnerKBaselineEnvelope

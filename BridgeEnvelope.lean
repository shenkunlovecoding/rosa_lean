import Std
import AffineLifetime
import OwnerBridges
import OwnerCompress
import BlockWinnerNoReentry

/-!
## M2 raw bridges to the M3 lifetime envelope

This file is deliberately an adapter.  It does not prove a new interval or
piece-count theorem; it makes the semantic bridge between the actual fixed-owner
bridge collections (`OwnerBridges.qOwnerBridges` / `kOwnerBridges`) and the
pointwise lifetime envelope (`AffineLifetime.Winner`) explicit.

The raw bridge winner is the route maximum among active bridges.  Equal routes
are retained by `Winner`; `BlockWinnerNoReentry.globalWinnerLabel` supplies the
canonical identity tie-break by `Bridge.kappa`.

For the K side, the raw bridge envelope is *not* the deletion-aware K winner.
`KBaselineWinner` is the explicit interface carrying the missing
`KDeleteFamily.Beats` obligation.
-/

namespace BridgeEnvelope

open Route RosBridge AffineLifetime OwnerBridges OwnerCompress KDeleteAbstract KDeleteROSA

variable {α : Type} [DecidableEq α]

/-! ### Lifting a bridge list -/

/-- Forget a bridge list to the pointwise affine lifetime candidates used by M3. -/
def ofBridgeList (bs : List Bridge) : List Candidate :=
  bs.map AffineLifetime.ofBridge

/-- The bridge embedding into affine lifetime candidates is injective. -/
theorem ofBridge_injective : Function.Injective AffineLifetime.ofBridge := by
  intro a b h
  have hp : a.p = b.p := by
    have hb : (a.p : Int) = (b.p : Int) := by
      simpa [AffineLifetime.ofBridge] using congrArg Candidate.birth h
    omega
  have hR : a.R = b.R := by
    have hd := congrArg Candidate.death h
    dsimp [AffineLifetime.ofBridge, RosBridge.Bridge.death] at hd
    omega
  have hL : a.L = b.L := by
    have hr := congrArg Candidate.route h
    have hbL := congrArg AffEnv.AffRoute.bL hr
    dsimp [AffineLifetime.ofBridge] at hbL
    omega
  have hu : a.u = b.u := by
    have hr := congrArg Candidate.route h
    have hbE := congrArg AffEnv.AffRoute.bE hr
    dsimp [AffineLifetime.ofBridge] at hbE
    omega
  cases a with
  | mk ap au aL aR =>
  cases b with
  | mk bp bu bL bR =>
  simp only [RosBridge.Bridge.mk.injEq]
  exact ⟨hp, hu, hL, hR⟩

@[simp] theorem mem_ofBridgeList {b : Bridge} {bs : List Bridge} :
    AffineLifetime.ofBridge b ∈ ofBridgeList bs ↔ b ∈ bs := by
  rw [ofBridgeList, List.mem_map]
  constructor
  · rintro ⟨c, hc, hcb⟩
    have hcb' : c = b := ofBridge_injective hcb
    simpa [hcb'] using hc
  · intro hb
    exact ⟨b, hb, rfl⟩

/-! ### Raw bridge winner semantics -/

/-- The actual route maximum among the active bridges of `bs`.  Ties are kept,
because ROSA's route order is a total preorder. -/
def BridgeWins (bs : List Bridge) (b : Bridge) (t : Nat) : Prop :=
  b ∈ bs ∧ b.Active t ∧
    ∀ c ∈ bs, c.Active t → Route.rle (c.routeAt t) (b.routeAt t)

/-- The lifetime envelope winner is exactly the raw active route maximum. -/
theorem winner_iff_bridgeWins {bs : List Bridge} {b : Bridge} {t : Nat} :
    Winner (AffineLifetime.ofBridge b) (ofBridgeList bs) (t : Int) ↔
      BridgeWins bs b t := by
  constructor
  · rintro ⟨hmem, hactive, hwins⟩
    have hbridgeActive : b.Active t :=
      (AffineLifetime.ofBridge_active_nat_iff b t).mp hactive
    refine ⟨mem_ofBridgeList.mp hmem, hbridgeActive, ?_⟩
    intro c hc hcActive
    exact (AffineLifetime.ofBridge_wins_iff_route_rle b c t hbridgeActive hcActive).mp
      (hwins (AffineLifetime.ofBridge c) (mem_ofBridgeList.mpr hc)
        ((AffineLifetime.ofBridge_active_nat_iff c t).mpr hcActive))
  · rintro ⟨hmem, hactive, hwins⟩
    refine ⟨mem_ofBridgeList.mpr hmem,
      (AffineLifetime.ofBridge_active_nat_iff b t).mpr hactive, ?_⟩
    intro d hd hdActive
    rw [ofBridgeList, List.mem_map] at hd
    obtain ⟨c, hc, hcd⟩ := hd
    subst d
    have hcActive : c.Active t :=
      (AffineLifetime.ofBridge_active_nat_iff c t).mp hdActive
    exact (AffineLifetime.ofBridge_wins_iff_route_rle b c t hactive hcActive).mpr
      (hwins c hc hcActive)

/-- The winner's route is literally the `rmaxList` field of the active raw
bridges. -/
theorem bridgeWins_route_eq_fieldBridges {bs : List Bridge} {b : Bridge} {t : Nat}
    (h : BridgeWins bs b t) :
    b.routeAt t = OwnerCompress.fieldBridges bs t := by
  apply Route.rle_antisymm
  · apply rle_rmaxList
    rw [List.mem_map]
    exact ⟨b, h.1, by simp [h.2.1]⟩
  · unfold OwnerCompress.fieldBridges
    apply rmaxList_lub
    · exact Bridge.valid_routeAt b t h.2.1
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨c, hc, rfl⟩ := hr
      by_cases hcActive : c.Active t
      · simp only [hcActive, if_true]
        exact h.2.2 c hc hcActive
      · simp [hcActive]
        exact valid_rle_unmatched (b.routeAt t) (Bridge.valid_routeAt b t h.2.1)

/-- Conversely, an active member whose route equals the raw field is a winner. -/
theorem route_eq_fieldBridges_iff_bridgeWins {bs : List Bridge} {b : Bridge} {t : Nat}
    (hmem : b ∈ bs) (hactive : b.Active t) :
    b.routeAt t = OwnerCompress.fieldBridges bs t ↔ BridgeWins bs b t := by
  constructor
  · intro heq
    refine ⟨hmem, hactive, ?_⟩
    intro c hc hcActive
    have hmemField : c.routeAt t ∈
        bs.map (fun x => if x.Active t then x.routeAt t else Route.unmatched) := by
      rw [List.mem_map]
      exact ⟨c, hc, by simp [hcActive]⟩
    have hleField : Route.rle (c.routeAt t) (OwnerCompress.fieldBridges bs t) := by
      unfold OwnerCompress.fieldBridges
      exact rle_rmaxList _ _ hmemField
    simpa [heq] using hleField
  · exact bridgeWins_route_eq_fieldBridges

/-- Candidate-level version of `bridgeWins_route_eq_fieldBridges`. -/
theorem winner_route_eq_fieldBridges {bs : List Bridge} {b : Bridge} {t : Nat}
    (h : Winner (AffineLifetime.ofBridge b) (ofBridgeList bs) (t : Int)) :
    b.routeAt t = OwnerCompress.fieldBridges bs t :=
  bridgeWins_route_eq_fieldBridges (winner_iff_bridgeWins.mp h)

/-! ### Canonical identity tie-break -/

/-- `BridgeWins` is the same predicate as the existing raw canonical-identity
winner predicate. -/
theorem bridgeWins_iff_globalLocalWins {bs : List Bridge} {b : Bridge} {t : Nat} :
    BridgeWins bs b t ↔ BlockWinnerNoReentry.globalLocalWins bs b t := by
  constructor
  · rintro ⟨hmem, hactive, hwins⟩
    refine ⟨hmem, hactive, ?_⟩
    intro c hc hcActive hstrict
    have hcbK : klexLE b.kappa c.kappa :=
      (route_better_iff_kappa b c t hactive hcActive).mp (hwins c hc hcActive)
    exact hstrict.2 (klexLE_antisymm hstrict.1 hcbK)
  · rintro ⟨hmem, hactive, hno⟩
    refine ⟨hmem, hactive, ?_⟩
    intro c hc hcActive
    by_cases hcb : Route.rle (c.routeAt t) (b.routeAt t)
    · exact hcb
    · have hbc : Route.rle (b.routeAt t) (c.routeAt t) := by
        rcases Route.rle_total (b.routeAt t) (c.routeAt t) with h | h
        · exact h
        · exact absurd h hcb
      have hle_cb : klexLE c.kappa b.kappa :=
        (route_better_iff_kappa c b t hcActive hactive).mp hbc
      by_cases heq : c.kappa = b.kappa
      · have hle_bc : klexLE b.kappa c.kappa := by
          rw [heq]
          unfold klexLE
          omega
        exact (route_better_iff_kappa b c t hactive hcActive).mpr hle_bc
      · exact False.elim (hno c hc hcActive ⟨hle_cb, heq⟩)

/-- Raw route winners with different Kappa identities cannot coexist. -/
theorem bridgeWins_kappa_unique {bs : List Bridge} {b c : Bridge} {t : Nat}
    (hb : BridgeWins bs b t) (hc : BridgeWins bs c t) : b.kappa = c.kappa := by
  have hbglobal : BlockWinnerNoReentry.globalLocalWins bs b t :=
    (bridgeWins_iff_globalLocalWins).mp hb
  have hcglobal : BlockWinnerNoReentry.globalLocalWins bs c t :=
    (bridgeWins_iff_globalLocalWins).mp hc
  exact BlockWinnerNoReentry.globalLocalWins_kappa_unique hbglobal hcglobal

/-- `AffineLifetime.Winner` over the lifted list is the same as the existing
canonical raw winner predicate. -/
theorem winner_iff_globalLocalWins {bs : List Bridge} {b : Bridge} {t : Nat} :
    Winner (AffineLifetime.ofBridge b) (ofBridgeList bs) (t : Int) ↔
      BlockWinnerNoReentry.globalLocalWins bs b t :=
  winner_iff_bridgeWins.trans bridgeWins_iff_globalLocalWins

/-- The canonical raw winner label is exactly the label of an affine lifetime
winner; the label is `kappa`, so equal-route ties have one canonical identity. -/
theorem canonicalWinner_eq_some_iff (bs : List Bridge) (t : Nat) (κ : Int × Int) :
    BlockWinnerNoReentry.globalWinnerLabel bs t = some κ ↔
      ∃ b, Winner (AffineLifetime.ofBridge b) (ofBridgeList bs) (t : Int) ∧
        b.kappa = κ := by
  rw [BlockWinnerNoReentry.globalWinnerLabel_eq_some_iff]
  constructor
  · rintro ⟨b, hb, hbκ⟩
    exact ⟨b, winner_iff_globalLocalWins.mpr hb, hbκ⟩
  · rintro ⟨b, hb, hbκ⟩
    exact ⟨b, winner_iff_globalLocalWins.mp hb, hbκ⟩

/-! ### Fixed Q-owner bridge collection -/

/-- The fixed Q-owner collection as lifetime candidates. -/
def qOwnerCandidates (q k : Nat → α) (Tq Tk a b c d p : Nat) : List Candidate :=
  ofBridgeList (OwnerBridges.qOwnerBridges q k Tq Tk a b c d p)

/-- **Q-side exact bridge.**  The lifetime envelope winner on
`qOwnerCandidates` is exactly the active raw route maximum on
`qOwnerBridges`. -/
theorem qOwnerCandidates_winner_iff_bridgeWins
    {q k : Nat → α} {Tq Tk a b c d p : Nat} {x : Bridge} {t : Nat} :
    Winner (AffineLifetime.ofBridge x)
        (qOwnerCandidates q k Tq Tk a b c d p) (t : Int) ↔
      BridgeWins (OwnerBridges.qOwnerBridges q k Tq Tk a b c d p) x t := by
  simpa [qOwnerCandidates] using
    (winner_iff_bridgeWins (bs := OwnerBridges.qOwnerBridges q k Tq Tk a b c d p)
      (b := x) (t := t))

/-- Route-value form of the Q-side exact bridge. -/
theorem qOwnerCandidates_winner_route_eq_fieldBridges
    {q k : Nat → α} {Tq Tk a b c d p : Nat} {x : Bridge} {t : Nat}
    (h : Winner (AffineLifetime.ofBridge x)
        (qOwnerCandidates q k Tq Tk a b c d p) (t : Int)) :
    x.routeAt t = OwnerCompress.fieldBridges
      (OwnerBridges.qOwnerBridges q k Tq Tk a b c d p) t :=
  winner_route_eq_fieldBridges (bs := OwnerBridges.qOwnerBridges q k Tq Tk a b c d p)
    (b := x) (t := t) (by simpa [qOwnerCandidates] using h)

/-- Canonical Q-owner winner identity, using the existing `kappa` label. -/
theorem qOwnerCandidates_canonicalWinner_eq_some_iff
    {q k : Nat → α} {Tq Tk a b c d p : Nat} {t : Nat} {κ : Int × Int} :
    BlockWinnerNoReentry.globalWinnerLabel
        (OwnerBridges.qOwnerBridges q k Tq Tk a b c d p) t = some κ ↔
      ∃ x, Winner (AffineLifetime.ofBridge x)
          (qOwnerCandidates q k Tq Tk a b c d p) (t : Int) ∧ x.kappa = κ := by
  simpa [qOwnerCandidates] using
    (canonicalWinner_eq_some_iff
      (bs := OwnerBridges.qOwnerBridges q k Tq Tk a b c d p) (t := t) (κ := κ))

/-! ### Fixed K-owner bridge collection: raw envelope and baseline interface -/

/-- The fixed K-owner collection as lifetime candidates.  This is the **raw**
bridge envelope, not the deletion-aware K cut winner. -/
def kOwnerCandidates (q k : Nat → α) (Tq Tk a b c d u : Nat) : List Candidate :=
  ofBridgeList (OwnerBridges.kOwnerBridges q k Tq Tk a b c d u)

/-- Raw K-owner bridge envelope: exactly the active route maximum on
`kOwnerBridges`. -/
theorem kOwnerCandidates_rawWinner_iff_bridgeWins
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {x : Bridge} {t : Nat} :
    Winner (AffineLifetime.ofBridge x)
        (kOwnerCandidates q k Tq Tk a b c d u) (t : Int) ↔
      BridgeWins (OwnerBridges.kOwnerBridges q k Tq Tk a b c d u) x t := by
  simpa [kOwnerCandidates] using
    (winner_iff_bridgeWins (bs := OwnerBridges.kOwnerBridges q k Tq Tk a b c d u)
      (b := x) (t := t))

/-- Canonical raw K-owner identity.  The name says `raw`: this does not include
the deletion baseline. -/
theorem kOwnerCandidates_rawCanonicalWinner_eq_some_iff
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {t : Nat} {κ : Int × Int} :
    BlockWinnerNoReentry.globalWinnerLabel
        (OwnerBridges.kOwnerBridges q k Tq Tk a b c d u) t = some κ ↔
      ∃ x, Winner (AffineLifetime.ofBridge x)
          (kOwnerCandidates q k Tq Tk a b c d u) (t : Int) ∧ x.kappa = κ := by
  simpa [kOwnerCandidates] using
    (canonicalWinner_eq_some_iff
      (bs := OwnerBridges.kOwnerBridges q k Tq Tk a b c d u) (t := t) (κ := κ))

/-- The deletion-baseline-aware K winner interface.  This is intentionally
separate from `BridgeWins`: callers must supply the concrete
`KDeleteFamily` before using it. -/
def KBaselineWinner (D : KDeleteFamily) (u : Nat) (bs : List Bridge)
    (b : Bridge) (t : Nat) : Prop :=
  BlockWinnerNoReentry.kLocalWins D u bs b t

/-- Raw route maximality plus the explicit deletion-baseline obligation is
exactly the K-suffix winner.  In particular, a raw `Winner` alone cannot
discharge `D.Beats`. -/
theorem kBaselineWinner_iff_rawWinner_and_beats
    {D : KDeleteFamily} {u : Nat} {bs : List Bridge} {b : Bridge} {t : Nat} :
    KBaselineWinner D u bs b t ↔
      BridgeWins bs b t ∧ b.u = u ∧ D.Beats b t := by
  unfold KBaselineWinner BlockWinnerNoReentry.kLocalWins
    BlockWinnerNoReentry.kSuffixWins
  constructor
  · rintro ⟨hmem, hu, hactive, hbeats, hno⟩
    exact ⟨(bridgeWins_iff_globalLocalWins).mpr ⟨hmem, hactive, hno⟩, hu, hbeats⟩
  · rintro ⟨hbw, hu, hbeats⟩
    have hglobal := (bridgeWins_iff_globalLocalWins).mp hbw
    exact ⟨hglobal.1, hu, hglobal.2.1, hbeats, hglobal.2.2⟩

/-- ROSA specialization of the K baseline interface.  The baseline is the
concrete delete-`k[u]` family; no raw-envelope theorem is being substituted for
it. -/
def RosaKBaselineWinner {α : Type} [DecidableEq α] (q k : Nat → α) (u : Nat)
    (bs : List Bridge) (b : Bridge) (t : Nat) : Prop :=
  KBaselineWinner (KDeleteROSA.rosaKDelete q k u) u bs b t

/-- Canonical label for the deletion-aware K winner.  This is the correct
canonical identity for K cut comparisons; it is not the raw K label above. -/
theorem rosaKBaselineWinner_label_eq_some_iff
    {q k : Nat → α} {u : Nat} {bs : List Bridge} {t : Nat} {κ : Int × Int} :
    BlockWinnerNoReentry.kWinnerLabel (KDeleteROSA.rosaKDelete q k u) u bs t = some κ ↔
      ∃ b, RosaKBaselineWinner q k u bs b t ∧ b.kappa = κ := by
  unfold RosaKBaselineWinner KBaselineWinner
  exact (BlockWinnerNoReentry.kWinnerLabel_eq_some_iff
    (D := KDeleteROSA.rosaKDelete q k u) (u := u) (bs := bs) (t := t) (κ := κ)
    (hunique := fun _ _ _ hb hc =>
      BlockWinnerNoReentry.kLocalWins_kappa_unique hb hc))

end BridgeEnvelope

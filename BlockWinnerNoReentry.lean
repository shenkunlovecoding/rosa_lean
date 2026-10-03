import Std
import Phase12b
import KDeleteROSA
import OwnerBridges
import WinnerPieces

/-!
## Canonical winner identity: local ROSA interval theorems

This file isolates the canonical-identity part of Phase 12b.  A ROSA route
comparison is a total preorder: different bridges may have the same `kappa`
and therefore the same route priority.  We canonicalise the *identity* by the
normalised priority `kappa`; all bridges in one `kappa` class have the same route
line, so this is the natural identity used by the no-re-entry count.

The main results are local to one owner:

* `qLocalWins_iff_commonBirth` identifies the actual Q-owner repair winner with
  `CommonBirth.cbWins` and hence with a closed interval.
* `kLocalWins_rosa_iff` identifies the deletion-baseline-aware K-owner winner
  with the interval from `rosaKDelete` / `KSkyline`.
* `qKeyWins_isInterval` and `kKeyWins_isInterval` lift those per-bridge intervals
  to the canonical `kappa` identity classes.
* the final `*_segments_le_three_mul_on` theorems use the Phase 12b interval
  counting argument on the labels actually present in a finite block list.

No axiom or `sorry` is used.  The global cross-block claim remains separate:
the last section records the precise missing interval hypothesis and a concrete
lifetime counterexample when it is absent.
-/

namespace BlockWinnerNoReentry

open Route RosBridge CommonBirth KSkyline KDeleteAbstract

/-! ### A finite canonical label from a winner predicate -/

/-- Choose the label of an arbitrary witness of `P · t`; return `none` when no
witness exists. -/
noncomputable def winnerLabel {β : Type} (P : β → Nat → Prop)
    (label : β → Int × Int) : Nat → Option (Int × Int) :=
  fun t => by
    classical
    exact if h : ∃ b, P b t then some (label (Classical.choose h)) else none

/-- If all witnesses at a fixed time have the same label, the chosen label is
exactly the label of every witness. -/
theorem winnerLabel_eq_some_iff {β : Type} {P : β → Nat → Prop}
    {label : β → Int × Int} {t : Nat} {κ : Int × Int}
    (hunique : ∀ t b c, P b t → P c t → label b = label c) :
    winnerLabel P label t = some κ ↔ ∃ b, P b t ∧ label b = κ := by
  unfold winnerLabel
  constructor
  · intro h
    by_cases hex : ∃ b, P b t
    · rw [dif_pos hex] at h
      exact ⟨Classical.choose hex, Classical.choose_spec hex, Option.some.inj h⟩
    · rw [dif_neg hex] at h
      simp at h
  · rintro ⟨b, hb, hbκ⟩
    have hex : ∃ b, P b t := ⟨b, hb⟩
    rw [dif_pos hex]
    have hch := Classical.choose_spec hex
    have hlabel : label (Classical.choose hex) = κ := by
      rw [← hbκ]
      exact hunique t (Classical.choose hex) b hch hb
    rw [hlabel]

/-! ### Q side: actual bridges through `CommonBirth` -/

/-- The common-birth representation of a bridge: priority and expiry. -/
def qCBCand (b : Bridge) : CBCand := ⟨b.kappa, b.death⟩

/-- Fixed-Q-owner local winner predicate.  The membership/owner fields identify
the actual bridge rather than an arbitrary bridge with the same priority. -/
def qLocalWins (p : Nat) (bs : List Bridge) (b : Bridge) (t : Nat) : Prop :=
  b ∈ bs ∧ b.p = p ∧ cbWins p (bs.map qCBCand) (qCBCand b) t

/-- Explicit unfolded form of `qLocalWins`, used to lift identities. -/
theorem qLocalWins_iff {p : Nat} {bs : List Bridge} {b : Bridge} {t : Nat} :
    qLocalWins p bs b t ↔
      b ∈ bs ∧ b.p = p ∧ p ≤ t ∧ t ≤ b.death ∧
        ∀ c ∈ bs, klexLT c.kappa b.kappa → c.death < t := by
  unfold qLocalWins cbWins
  constructor
  · rintro ⟨hmem, hp, hpt, hte, hno⟩
    refine ⟨hmem, hp, hpt, hte, ?_⟩
    intro c hc hbetter
    exact hno (qCBCand c) (List.mem_map.mpr ⟨c, hc, rfl⟩) hbetter
  · rintro ⟨hmem, hp, hpt, hte, hno⟩
    refine ⟨hmem, hp, hpt, hte, ?_⟩
    intro x hx hbetter
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    exact hno c hc hbetter

/-- **Actual Q theorem.**  The fixed-Q-owner winner is the closed common-birth
interval from `CommonBirth.common_birth_winner_iff`. -/
theorem qLocalWins_iff_commonBirth {p : Nat} {bs : List Bridge} {b : Bridge} {t : Nat} :
    qLocalWins p bs b t ↔
      b ∈ bs ∧ b.p = p ∧ cbF p (bs.map qCBCand) (qCBCand b) ≤ t ∧ t ≤ b.death := by
  constructor
  · rintro ⟨hmem, hp, ht⟩
    exact ⟨hmem, hp, (common_birth_winner_iff p (bs.map qCBCand) (qCBCand b) t).mp ht⟩
  · rintro ⟨hmem, hp, ht⟩
    exact ⟨hmem, hp, (common_birth_winner_iff p (bs.map qCBCand) (qCBCand b) t).mpr ht⟩

/-- A fixed Q-side bridge has an interval winner set. -/
theorem qLocalWins_isInterval (p : Nat) (bs : List Bridge) (b : Bridge) :
    Phase12b.IsInterval (fun t => qLocalWins p bs b t) := by
  intro i hi k hk j hij hjk
  obtain ⟨hmem, hp, hcbi⟩ := hi
  obtain ⟨_, _, hcbk⟩ := hk
  exact ⟨hmem, hp, Phase12b.qCBCand_isInterval (bs.map qCBCand) (qCBCand b)
    i hcbi k hcbk j hij hjk⟩

/-- Two simultaneous Q-side local winners have the same canonical `kappa`. -/
theorem qLocalWins_kappa_unique {p : Nat} {bs : List Bridge} {b c : Bridge} {t : Nat}
    (hb : qLocalWins p bs b t) (hc : qLocalWins p bs c t) : b.kappa = c.kappa := by
  have hb' := qLocalWins_iff.mp hb
  have hc' := qLocalWins_iff.mp hc
  have hbt : b.Active t := by
    constructor
    · rw [hb'.2.1]
      exact hb'.2.2.1
    · simpa [Bridge.death] using hb'.2.2.2.1
  have hct : c.Active t := by
    constructor
    · rw [hc'.2.1]
      exact hc'.2.2.1
    · simpa [Bridge.death] using hc'.2.2.2.1
  rcases Route.rle_total (b.routeAt t) (c.routeAt t) with hbc | hcb
  · have hle : klexLE c.kappa b.kappa :=
      (route_better_iff_kappa c b t hct hbt).mp hbc
    by_cases heq : c.kappa = b.kappa
    · exact heq.symm
    · have hstrict : klexLT c.kappa b.kappa := ⟨hle, heq⟩
      have := hb'.2.2.2.2 c hc'.1 hstrict
      omega
  · have hle : klexLE b.kappa c.kappa :=
      (route_better_iff_kappa b c t hbt hct).mp hcb
    by_cases heq : b.kappa = c.kappa
    · exact heq
    · have hstrict : klexLT b.kappa c.kappa := ⟨hle, heq⟩
      have := hc'.2.2.2.2 b hb'.1 hstrict
      omega

/-- Canonical Q identity classes: a class wins when one of its actual bridges
wins locally. -/
def qKeyWins (p : Nat) (bs : List Bridge) (κ : Int × Int) (t : Nat) : Prop :=
  ∃ b, qLocalWins p bs b t ∧ b.kappa = κ

/-- **Q canonical-identity interval.**  Every `kappa` winner class is an
interval. -/
theorem qKeyWins_isInterval (p : Nat) (bs : List Bridge) (κ : Int × Int) :
    Phase12b.IsInterval (fun t => qKeyWins p bs κ t) := by
  intro i hi k hk j hij hjk
  obtain ⟨b, hb, hbκ⟩ := hi
  obtain ⟨c, hc, hcκ⟩ := hk
  have hb' := qLocalWins_iff.mp hb
  have hc' := qLocalWins_iff.mp hc
  refine ⟨c, ?_, hcκ⟩
  rw [qLocalWins_iff]
  refine ⟨hc'.1, hc'.2.1, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro d hd hbetter
    have hbetter' : klexLT d.kappa b.kappa := by
      simpa [hcκ, hbκ] using hbetter
    have := hb'.2.2.2.2 d hd hbetter'
    omega

/-- The canonical Q winner label. -/
noncomputable def qWinnerLabel (p : Nat) (bs : List Bridge) : Nat → Option (Int × Int) :=
  winnerLabel (fun b t => qLocalWins p bs b t) Bridge.kappa

theorem qWinnerLabel_eq_some_iff (p : Nat) (bs : List Bridge) (t : Nat)
    (κ : Int × Int) :
    qWinnerLabel p bs t = some κ ↔ qKeyWins p bs κ t := by
  unfold qWinnerLabel qKeyWins
  exact winnerLabel_eq_some_iff
    (P := fun b t => qLocalWins p bs b t) (label := Bridge.kappa) (κ := κ)
    (hunique := fun _ _ _ hb hc => qLocalWins_kappa_unique hb hc)

theorem qWinnerLabel_isInterval_some (p : Nat) (bs : List Bridge) (κ : Int × Int) :
    Phase12b.IsInterval (fun t => qWinnerLabel p bs t = some κ) := by
  intro i hi k hk j hij hjk
  rw [qWinnerLabel_eq_some_iff] at hi hk ⊢
  exact qKeyWins_isInterval p bs κ i hi k hk j hij hjk


/-! ### K side: deletion-baseline-aware `rosaKDelete` -/

/-- The KSkyline winner predicate.  This is exactly the left-hand side of
`KSkyline.k_suffix_winner_iff`. -/
def kSuffixWins (D : KDeleteFamily) (bs : List Bridge) (b : Bridge) (t : Nat) : Prop :=
  b.Active t ∧ D.Beats b t ∧
    ∀ c ∈ bs, c.Active t → ¬ klexLT c.kappa b.kappa

/-- Fixed-K-owner local winner predicate: actual membership, actual owner, and
the deletion-baseline-aware suffix winner. -/
def kLocalWins (D : KDeleteFamily) (u : Nat) (bs : List Bridge) (b : Bridge)
    (t : Nat) : Prop :=
  b ∈ bs ∧ b.u = u ∧ kSuffixWins D bs b t

/-- **Actual K theorem, ROSA form.**  With the deletion baseline `rosaKDelete
q k u`, `rosa_k_suffix_winner_iff` makes the local winner an exact interval. -/
theorem kLocalWins_rosa_iff {α : Type} [DecidableEq α] {q k : Nat → α}
    {u : Nat} {bs : List Bridge} {b : Bridge}
    (hreal : ∀ c ∈ bs, klexLT c.kappa b.kappa → KDeleteROSA.RealisedK q k u c)
    (hreach : ∀ c ∈ bs, klexLT c.kappa b.kappa → c.shadowStart ≤ (b.p : Int))
    {d : Nat}
    (hdlow : ∀ t, b.p ≤ t → t < d → ¬ (KDeleteROSA.rosaKDelete q k u).Beats b t)
    (hdhigh : ∀ t, d ≤ t → t ≤ b.death → (KDeleteROSA.rosaKDelete q k u).Beats b t)
    {M : Nat}
    (hM : ∀ c ∈ bs, klexLT c.kappa b.kappa → c.death ≤ M)
    (hMat : M < b.p ∨ ∃ c ∈ bs, klexLT c.kappa b.kappa ∧ c.death = M) :
    kLocalWins (KDeleteROSA.rosaKDelete q k u) u bs b t ↔
      b ∈ bs ∧ b.u = u ∧ max b.p (max d (M + 1)) ≤ t ∧ t ≤ b.death := by
  constructor
  · rintro ⟨hmem, hu, hwin⟩
    exact ⟨hmem, hu,
      (KDeleteROSA.rosa_k_suffix_winner_iff (q := q) (k := k) (u := u)
        (others := bs) (b := b) hreal hreach hdlow hdhigh hM hMat t).mp hwin⟩
  · rintro ⟨hmem, hu, hwin⟩
    exact ⟨hmem, hu,
      (KDeleteROSA.rosa_k_suffix_winner_iff (q := q) (k := k) (u := u)
        (others := bs) (b := b) hreal hreach hdlow hdhigh hM hMat t).mpr hwin⟩

/-- A fixed K-side bridge whose KSkyline hypotheses have been supplied has an
interval winner set. -/
theorem kLocalWins_isInterval_of_skyline {D : KDeleteFamily} {u : Nat}
    {bs : List Bridge} {b : Bridge}
    (htrim : TrimClosed D)
    (hshadow : ∀ c ∈ bs, klexLT c.kappa b.kappa → HasPrebirthShadow D c)
    (hreach : ∀ c ∈ bs, klexLT c.kappa b.kappa → c.shadowStart ≤ (b.p : Int))
    {d M : Nat}
    (hdlow : ∀ t, b.p ≤ t → t < d → ¬ D.Beats b t)
    (hdhigh : ∀ t, d ≤ t → t ≤ b.death → D.Beats b t)
    (hM : ∀ c ∈ bs, klexLT c.kappa b.kappa → c.death ≤ M)
    (hMat : M < b.p ∨ ∃ c ∈ bs, klexLT c.kappa b.kappa ∧ c.death = M) :
    Phase12b.IsInterval (fun t => kLocalWins D u bs b t) := by
  intro i hi k hk j hij hjk
  obtain ⟨hmem, hu, hwi⟩ := hi
  obtain ⟨_, _, hwk⟩ := hk
  have hwj : kSuffixWins D bs b j := by
    have hiff := KSkyline.k_suffix_winner_iff (D := D) (others := bs) (b := b)
      htrim hshadow hreach hdlow hdhigh hM hMat
    unfold kSuffixWins at hwi hwk ⊢
    rw [hiff] at hwi hwk ⊢
    exact ⟨Nat.le_trans hwi.1 hij, Nat.le_trans hjk hwk.2⟩
  exact ⟨hmem, hu, hwj⟩

/-- A ROSA window is exactly the finite list of hypotheses needed to apply the
deletion-baseline-aware K skyline theorem to one bridge. -/
def HasRosaKWindow {α : Type} [DecidableEq α] (q k : Nat → α) (u : Nat)
    (bs : List Bridge) (b : Bridge) : Prop :=
  ∃ d M : Nat,
    (∀ c ∈ bs, klexLT c.kappa b.kappa → KDeleteROSA.RealisedK q k u c) ∧
    (∀ c ∈ bs, klexLT c.kappa b.kappa → c.shadowStart ≤ (b.p : Int)) ∧
    (∀ t, b.p ≤ t → t < d → ¬ (KDeleteROSA.rosaKDelete q k u).Beats b t) ∧
    (∀ t, d ≤ t → t ≤ b.death → (KDeleteROSA.rosaKDelete q k u).Beats b t) ∧
    (∀ c ∈ bs, klexLT c.kappa b.kappa → c.death ≤ M) ∧
    (M < b.p ∨ ∃ c ∈ bs, klexLT c.kappa b.kappa ∧ c.death = M)

/-- `rosaKDelete`/`KSkyline` discharges the local interval obligation whenever a
ROSA window is supplied. -/
theorem kLocalWins_rosa_isInterval_of_window {α : Type} [DecidableEq α]
    {q k : Nat → α} {u : Nat} {bs : List Bridge} {b : Bridge}
    (hwin : HasRosaKWindow q k u bs b) :
    Phase12b.IsInterval (fun t => kLocalWins (KDeleteROSA.rosaKDelete q k u) u bs b t) := by
  rcases hwin with ⟨d, M, hreal, hreach, hdlow, hdhigh, hM, hMat⟩
  intro i hi l hl j hij hjl
  obtain ⟨hmem, hu, hwi⟩ := hi
  obtain ⟨_, _, hwl⟩ := hl
  have hwj := Phase12b.kSuffixWinner_isInterval
    (KDeleteROSA.rosa_trim_closed q k u)
    (fun c hc hb => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hreal c hc hb
      exact KDeleteROSA.rosa_has_prebirth_shadow q k u c h1 h2 h3 h4 h5)
    hreach hdlow hdhigh hM hMat i hwi l hwl j hij hjl
  exact ⟨hmem, hu, hwj⟩

/-- Same-owner, same-`kappa` bridges have the same birth.  This is what turns
the K-side identity class into one contiguous canonical interval. -/
theorem bridge_p_eq_of_same_owner_and_kappa {b c : Bridge}
    (hu : b.u = c.u) (hk : b.kappa = c.kappa) : b.p = c.p := by
  have h2 := congrArg Prod.snd hk
  unfold Bridge.kappa at h2
  rw [hu] at h2
  omega

/-- Equal `kappa` bridges have equal routes while both are active. -/
theorem bridge_routeAt_eq_of_kappa_eq {b c : Bridge} {t : Nat}
    (hb : b.Active t) (hc : c.Active t) (hk : b.kappa = c.kappa) :
    b.routeAt t = c.routeAt t := by
  rw [Phase12b.bridge_route_eq_routeOfKappa b t hb,
    Phase12b.bridge_route_eq_routeOfKappa c t hc]
  unfold Phase12b.routeOfKappa
  rw [show b.kappa.1 = c.kappa.1 from congrArg Prod.fst hk,
    show b.kappa.2 = c.kappa.2 from congrArg Prod.snd hk]

/-- `D.Beats` depends only on the route at the current time. -/
theorem kdelete_beats_congr_route {D : KDeleteFamily} {b c : Bridge} {t : Nat}
    (h : b.routeAt t = c.routeAt t) : D.Beats b t ↔ D.Beats c t := by
  unfold KDeleteFamily.Beats
  rw [h]

/-- Two simultaneous K-side local winners have the same canonical `kappa`. -/
theorem kLocalWins_kappa_unique {D : KDeleteFamily} {u : Nat} {bs : List Bridge}
    {b c : Bridge} {t : Nat}
    (hb : kLocalWins D u bs b t) (hc : kLocalWins D u bs c t) :
    b.kappa = c.kappa := by
  have hbi := hb.2.2
  have hci := hc.2.2
  rcases Route.rle_total (b.routeAt t) (c.routeAt t) with hbc | hcb
  · have hle : klexLE c.kappa b.kappa :=
      (route_better_iff_kappa c b t hci.1 hbi.1).mp hbc
    by_cases heq : c.kappa = b.kappa
    · exact heq.symm
    · have hstrict : klexLT c.kappa b.kappa := ⟨hle, heq⟩
      exact False.elim (hbi.2.2 c hc.1 hci.1 hstrict)
  · have hle : klexLE b.kappa c.kappa :=
      (route_better_iff_kappa b c t hbi.1 hci.1).mp hcb
    by_cases heq : b.kappa = c.kappa
    · exact heq
    · have hstrict : klexLT b.kappa c.kappa := ⟨hle, heq⟩
      exact False.elim (hci.2.2 b hb.1 hbi.1 hstrict)

/-- Canonical K identity classes. -/
def kKeyWins (D : KDeleteFamily) (u : Nat) (bs : List Bridge)
    (κ : Int × Int) (t : Nat) : Prop :=
  ∃ b, kLocalWins D u bs b t ∧ b.kappa = κ

/-- **K canonical-identity interval.**  Assuming the local KSkyline interval for
each bridge in the owner family, every canonical `kappa` class is an interval. -/
theorem kKeyWins_isInterval {D : KDeleteFamily} {u : Nat} {bs : List Bridge}
    (hlocal : ∀ b ∈ bs, Phase12b.IsInterval (fun t => kLocalWins D u bs b t))
    (κ : Int × Int) :
    Phase12b.IsInterval (fun t => kKeyWins D u bs κ t) := by
  intro i hi k hk j hij hjk
  obtain ⟨b, hb, hbκ⟩ := hi
  obtain ⟨c, hc, hcκ⟩ := hk
  have hκ : b.kappa = c.kappa := by rw [hbκ, hcκ]
  have hu : b.u = c.u := by rw [hb.2.1, hc.2.1]
  have hp : b.p = c.p := bridge_p_eq_of_same_owner_and_kappa hu hκ
  have hbwin := hb.2.2
  have hcwin := hc.2.2
  have hc_active_i : c.Active i := by
    constructor
    · rw [← hp]
      exact hbwin.1.1
    · have := hcwin.1.2
      omega
  have hroute : c.routeAt i = b.routeAt i := by
    exact bridge_routeAt_eq_of_kappa_eq hc_active_i hbwin.1 hκ.symm
  have hbeats_c : D.Beats c i :=
    (kdelete_beats_congr_route (D := D) hroute).mpr hbwin.2.1
  have hno_c : ∀ d ∈ bs, d.Active i → ¬ klexLT d.kappa c.kappa := by
    intro d hd hdact hdlt
    have hdlt' : klexLT d.kappa b.kappa := by
      simpa [hκ] using hdlt
    exact hbwin.2.2 d hd hdact hdlt'
  have hcwin_i : kLocalWins D u bs c i := ⟨hc.1, hc.2.1, ⟨hc_active_i, hbeats_c, hno_c⟩⟩
  have hcwin_k : kLocalWins D u bs c k := ⟨hc.1, hc.2.1, hc.2.2⟩
  exact ⟨c, hlocal c hc.1 i hcwin_i k hcwin_k j hij hjk, hcκ⟩

/-- The canonical K winner label. -/
noncomputable def kWinnerLabel (D : KDeleteFamily) (u : Nat) (bs : List Bridge) :
    Nat → Option (Int × Int) :=
  winnerLabel (fun b t => kLocalWins D u bs b t) Bridge.kappa

theorem kWinnerLabel_eq_some_iff {D : KDeleteFamily} {u : Nat} {bs : List Bridge}
    {t : Nat} {κ : Int × Int}
    (hunique : ∀ t b c, kLocalWins D u bs b t → kLocalWins D u bs c t →
      b.kappa = c.kappa) :
    kWinnerLabel D u bs t = some κ ↔ kKeyWins D u bs κ t := by
  unfold kWinnerLabel kKeyWins
  exact winnerLabel_eq_some_iff
    (P := fun b t => kLocalWins D u bs b t) (label := Bridge.kappa) (κ := κ)
    (hunique := fun t b c hb hc => hunique t b c hb hc)

theorem kWinnerLabel_isInterval_some {D : KDeleteFamily} {u : Nat} {bs : List Bridge}
    (hlocal : ∀ b ∈ bs, Phase12b.IsInterval (fun t => kLocalWins D u bs b t))
    (κ : Int × Int) :
    Phase12b.IsInterval (fun t => kWinnerLabel D u bs t = some κ) := by
  intro i hi k hk j hij hjk
  rw [kWinnerLabel_eq_some_iff (fun _ _ _ hb hc => kLocalWins_kappa_unique hb hc)] at hi hk ⊢
  exact kKeyWins_isInterval hlocal κ i hi k hk j hij hjk


/-! ### Phase 12b counting with interval assumptions only on used labels -/

/-- On-support version of `Phase12b.segStart_label_ne`: only labels actually
appearing in the finite support need interval winner sets. -/
theorem segStart_label_ne_on {α : Type} [DecidableEq α] {f : Nat → α} {s : List α}
    (hint : ∀ c ∈ s, Phase12b.IsInterval (fun t => f t = c))
    {t₁ t₂ : Nat} (h₂ : Phase12b.IsSegStart f t₂) (ht₂ : f t₂ ∈ s)
    (hlt : t₁ < t₂) : f t₁ ≠ f t₂ := by
  intro heq
  have hne : f t₂ ≠ f (t₂ - 1) := by
    rcases h₂ with h0 | h0
    · omega
    · exact h0
  exact hne (hint (f t₂) ht₂ t₁ heq t₂ rfl (t₂ - 1) (by omega) (by omega)).symm

/-- On-support pigeonhole: interval winner classes give at most one segment per
label that can actually occur. -/
theorem segStarts_le_of_subset_on {α : Type} [DecidableEq α] (f : Nat → α)
    {T : Nat} {s : List α}
    (hint : ∀ c ∈ s, Phase12b.IsInterval (fun t => f t = c))
    (hsub : ∀ t, t < T → f t ∈ s) :
    ((List.range T).filter (fun t => decide (Phase12b.IsSegStart f t))).length ≤ s.length := by
  have hnd : ((List.range T).filter (fun t => decide (Phase12b.IsSegStart f t))).Nodup :=
    List.Nodup.sublist (List.filter_sublist (p := fun t => decide (Phase12b.IsSegStart f t)))
      List.nodup_range
  have hinj : ∀ a ∈ (List.range T).filter (fun t => decide (Phase12b.IsSegStart f t)),
      ∀ b ∈ (List.range T).filter (fun t => decide (Phase12b.IsSegStart f t)), f a = f b → a = b := by
    intro a ha b hb hab
    by_cases hlt : a < b
    · have hbs : f b ∈ s := hsub b (List.mem_range.mp (List.mem_filter.mp hb).1)
      exact absurd hab (segStart_label_ne_on hint
        (of_decide_eq_true (List.mem_filter.mp hb).2) hbs hlt)
    · have hle : b ≤ a := Nat.le_of_not_lt hlt
      by_cases hgt : b < a
      · have has : f a ∈ s := hsub a (List.mem_range.mp (List.mem_filter.mp ha).1)
        exact absurd hab.symm (segStart_label_ne_on hint
          (of_decide_eq_true (List.mem_filter.mp ha).2) has hgt)
      · omega
  have hsub2 : ∀ c ∈ (List.range T).filter (fun t => decide (Phase12b.IsSegStart f t)) |>.map f, c ∈ s := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact hsub t (List.mem_range.mp (List.mem_filter.mp ht).1)
  have := List.Nodup.length_le_of_subset
    (Phase12b.nodup_map_of_pairwise_inj hinj hnd) hsub2
  rwa [List.length_map] at this

/-- On-support `≤3m` bound.  This is the exact interface used below: the label
`none` of a partial canonical winner is not required to have an interval
preimage, only labels that occur in the finite candidate blocks are. -/
theorem segments_le_three_mul_of_isInterval_on {α : Type} [DecidableEq α]
    {blocks : List (List α)} (f : Nat → α) {T : Nat}
    (hlen : ∀ b ∈ blocks, b.length ≤ 3)
    (hint : ∀ c ∈ blocks.flatten, Phase12b.IsInterval (fun t => f t = c))
    (hsub : ∀ t, t < T → f t ∈ blocks.flatten) :
    ((List.range T).filter (fun t => decide (Phase12b.IsSegStart f t))).length ≤
      3 * blocks.length := by
  have h1 := segStarts_le_of_subset_on f hint hsub
  have h2 := Phase12b.flatten_length_le hlen
  omega

/-- The finite label blocks corresponding to a bridge block list. -/
def labelBlocks (blocks : List (List Bridge)) : List (List (Option (Int × Int))) :=
  blocks.map (fun bl => bl.map (fun b => some b.kappa))

theorem some_kappa_mem_labelBlocks {blocks : List (List Bridge)} {b : Bridge}
    (hb : b ∈ blocks.flatten) : some b.kappa ∈ (labelBlocks blocks).flatten := by
  rw [List.mem_flatten] at hb ⊢
  obtain ⟨bl, hbl, hbbl⟩ := hb
  refine ⟨bl.map (fun x => some x.kappa), ?_, ?_⟩
  · rw [labelBlocks, List.mem_map]
    exact ⟨bl, hbl, rfl⟩
  · rw [List.mem_map]
    exact ⟨b, hbbl, rfl⟩

/-- **Q owner bound.**  For one fixed Q-owner, the canonical `kappa` identity is
an interval (`CommonBirth`), so any partition of the bridge family into blocks of
size at most three yields at most `3m` winner segments. -/
theorem q_segments_le_three_mul {p T : Nat} (blocks : List (List Bridge))
    (hlen : ∀ bl ∈ blocks, bl.length ≤ 3)
    (hcover : ∀ t, t < T → ∃ b ∈ blocks.flatten, qLocalWins p blocks.flatten b t) :
    ((List.range T).filter (fun t =>
      decide (Phase12b.IsSegStart (qWinnerLabel p blocks.flatten) t))).length ≤
        3 * blocks.length := by
  rw [← show (labelBlocks blocks).length = blocks.length by simp [labelBlocks]]
  apply segments_le_three_mul_of_isInterval_on (f := qWinnerLabel p blocks.flatten)
    (blocks := labelBlocks blocks)
  · intro bl hbl
    rw [labelBlocks, List.mem_map] at hbl
    obtain ⟨orig, horig, rfl⟩ := hbl
    simpa using hlen orig horig
  · intro c hc
    cases c with
    | none =>
        rw [List.mem_flatten] at hc
        obtain ⟨l, hl, hnone⟩ := hc
        rw [labelBlocks, List.mem_map] at hl
        obtain ⟨orig, horig, rfl⟩ := hl
        simp at hnone
    | some κ =>
        exact qWinnerLabel_isInterval_some p blocks.flatten κ
  · intro t ht
    obtain ⟨b, hb, hwin⟩ := hcover t ht
    have hlabel : qWinnerLabel p blocks.flatten t = some b.kappa :=
      (qWinnerLabel_eq_some_iff p blocks.flatten t b.kappa).mpr ⟨b, hwin, rfl⟩
    rw [hlabel]
    exact some_kappa_mem_labelBlocks hb

/-- **K owner bound.**  The local intervals are discharged by
`rosaKDelete`/`KSkyline`; the resulting canonical `kappa` identity classes give
the exact `≤3m` bound for one fixed K-owner. -/
theorem k_segments_le_three_mul {α : Type} [DecidableEq α] {q k : Nat → α}
    {u T : Nat} (blocks : List (List Bridge))
    (hlen : ∀ bl ∈ blocks, bl.length ≤ 3)
    (hwindow : ∀ b ∈ blocks.flatten,
      HasRosaKWindow q k u blocks.flatten b)
    (hcover : ∀ t, t < T →
      ∃ b ∈ blocks.flatten,
        kLocalWins (KDeleteROSA.rosaKDelete q k u) u blocks.flatten b t) :
    ((List.range T).filter (fun t => decide
      (Phase12b.IsSegStart
        (kWinnerLabel (KDeleteROSA.rosaKDelete q k u) u blocks.flatten) t))).length ≤
        3 * blocks.length := by
  let D := KDeleteROSA.rosaKDelete q k u
  rw [← show (labelBlocks blocks).length = blocks.length by simp [labelBlocks]]
  have hlocal : ∀ b ∈ blocks.flatten, Phase12b.IsInterval
      (fun t => kLocalWins D u blocks.flatten b t) := by
    intro b hb
    exact kLocalWins_rosa_isInterval_of_window (hwindow b hb)
  change ((List.range T).filter (fun t => decide
      (Phase12b.IsSegStart (kWinnerLabel D u blocks.flatten) t))).length ≤
        3 * (labelBlocks blocks).length
  apply segments_le_three_mul_of_isInterval_on
    (f := kWinnerLabel D u blocks.flatten) (blocks := labelBlocks blocks)
  · intro bl hbl
    rw [labelBlocks, List.mem_map] at hbl
    obtain ⟨orig, horig, rfl⟩ := hbl
    simpa using hlen orig horig
  · intro c hc
    cases c with
    | none =>
        rw [List.mem_flatten] at hc
        obtain ⟨l, hl, hnone⟩ := hc
        rw [labelBlocks, List.mem_map] at hl
        obtain ⟨orig, horig, rfl⟩ := hl
        simp at hnone
    | some κ =>
        exact kWinnerLabel_isInterval_some hlocal κ
  · intro t ht
    obtain ⟨b, hb, hwin⟩ := hcover t ht
    have hlabel : kWinnerLabel D u blocks.flatten t = some b.kappa :=
      (kWinnerLabel_eq_some_iff
        (D := D) (u := u) (bs := blocks.flatten)
        (fun _ _ _ hab hcd => kLocalWins_kappa_unique hab hcd)).mpr ⟨b, hwin, rfl⟩
    rw [hlabel]
    exact some_kappa_mem_labelBlocks hb


/-! ### The exact remaining cross-block condition -/

/-- Global repair winner in a bridge list, before selecting a canonical tie
identity.  It is the literal route-max winner predicate written in `kappa`. -/
def globalLocalWins (bs : List Bridge) (b : Bridge) (t : Nat) : Prop :=
  b ∈ bs ∧ b.Active t ∧
    ∀ c ∈ bs, c.Active t → ¬ klexLT c.kappa b.kappa

/-- Simultaneous global winners have the same canonical `kappa`. -/
theorem globalLocalWins_kappa_unique {bs : List Bridge} {b c : Bridge} {t : Nat}
    (hb : globalLocalWins bs b t) (hc : globalLocalWins bs c t) : b.kappa = c.kappa := by
  rcases Route.rle_total (b.routeAt t) (c.routeAt t) with hbc | hcb
  · have hle : klexLE c.kappa b.kappa :=
      (route_better_iff_kappa c b t hc.2.1 hb.2.1).mp hbc
    by_cases heq : c.kappa = b.kappa
    · exact heq.symm
    · have hstrict : klexLT c.kappa b.kappa := ⟨hle, heq⟩
      exact False.elim (hb.2.2 c hc.1 hc.2.1 hstrict)
  · have hle : klexLE b.kappa c.kappa :=
      (route_better_iff_kappa b c t hb.2.1 hc.2.1).mp hcb
    by_cases heq : b.kappa = c.kappa
    · exact heq
    · have hstrict : klexLT b.kappa c.kappa := ⟨hle, heq⟩
      exact False.elim (hc.2.2 b hb.1 hb.2.1 hstrict)

/-- Canonical global winner identity. -/
noncomputable def globalWinnerLabel (bs : List Bridge) : Nat → Option (Int × Int) :=
  winnerLabel (fun b t => globalLocalWins bs b t) Bridge.kappa

theorem globalWinnerLabel_eq_some_iff (bs : List Bridge) (t : Nat) (κ : Int × Int) :
    globalWinnerLabel bs t = some κ ↔
      ∃ b, globalLocalWins bs b t ∧ b.kappa = κ := by
  unfold globalWinnerLabel
  exact winnerLabel_eq_some_iff
    (P := fun b t => globalLocalWins bs b t) (label := Bridge.kappa) (κ := κ)
    (hunique := fun _ _ _ hb hc => globalLocalWins_kappa_unique hb hc)

/-- **Exact global conditional bound.**  Once the canonical global identity has
interval classes on the labels actually occurring in the candidate blocks, the
same Phase 12b pigeonhole gives the real `≤3m` bound.  The hypothesis
`hcross` is precisely the cross-block obligation left open below. -/
theorem global_segments_le_three_mul {T : Nat} (blocks : List (List Bridge))
    (hlen : ∀ bl ∈ blocks, bl.length ≤ 3)
    (hcross : ∀ c ∈ (labelBlocks blocks).flatten,
      Phase12b.IsInterval (fun t => globalWinnerLabel blocks.flatten t = c))
    (hcover : ∀ t, t < T → ∃ b ∈ blocks.flatten, globalLocalWins blocks.flatten b t) :
    ((List.range T).filter (fun t =>
      decide (Phase12b.IsSegStart (globalWinnerLabel blocks.flatten) t))).length ≤
        3 * blocks.length := by
  rw [← show (labelBlocks blocks).length = blocks.length by simp [labelBlocks]]
  apply segments_le_three_mul_of_isInterval_on
    (f := globalWinnerLabel blocks.flatten) (blocks := labelBlocks blocks)
  · intro bl hbl
    rw [labelBlocks, List.mem_map] at hbl
    obtain ⟨orig, horig, rfl⟩ := hbl
    simpa using hlen orig horig
  · intro c hc
    cases c with
    | none =>
        rw [List.mem_flatten] at hc
        obtain ⟨l, hl, hnone⟩ := hc
        rw [labelBlocks, List.mem_map] at hl
        obtain ⟨orig, horig, rfl⟩ := hl
        simp at hnone
    | some κ =>
        exact hcross (some κ) hc
  · intro t ht
    obtain ⟨b, hb, hwin⟩ := hcover t ht
    have hlabel : globalWinnerLabel blocks.flatten t = some b.kappa :=
      (globalWinnerLabel_eq_some_iff blocks.flatten t b.kappa).mpr ⟨b, hwin, rfl⟩
    rw [hlabel]
    exact some_kappa_mem_labelBlocks hb

/-! ### A genuine cross-block counterexample

The following two causal-looking bridges have disjoint block labels but nested
lifetimes.  The first wins before the second is born, the second wins while it is
alive, and the first wins again after the second expires.  Thus the global
per-identity winner set is not an interval and global no-re-entry is false
without a cross-block hypothesis. -/

def reentryWeak : Bridge := ⟨2, 1, 1, 8⟩
def reentryStrong : Bridge := ⟨4, 3, 4, 2⟩
def reentryBlocks : List (List Bridge) := [[reentryWeak], [reentryStrong]]

/-- The first bridge wins at `3` and `7`, while the second wins at `5`. -/
theorem crossBlock_lifetime_reentry :
    globalLocalWins reentryBlocks.flatten reentryWeak 3 ∧
    globalLocalWins reentryBlocks.flatten reentryStrong 5 ∧
    globalLocalWins reentryBlocks.flatten reentryWeak 7 := by
  unfold globalLocalWins
  decide

/-- The canonical label sequence is exactly `weak, strong, weak`, so the
cross-block identity genuinely re-enters. -/
theorem crossBlock_canonical_reentry :
    globalWinnerLabel reentryBlocks.flatten 3 = some reentryWeak.kappa ∧
    globalWinnerLabel reentryBlocks.flatten 5 = some reentryStrong.kappa ∧
    globalWinnerLabel reentryBlocks.flatten 7 = some reentryWeak.kappa := by
  constructor
  · apply (globalWinnerLabel_eq_some_iff reentryBlocks.flatten 3 reentryWeak.kappa).mpr
    refine ⟨reentryWeak, ?_, rfl⟩
    unfold globalLocalWins
    decide
  constructor
  · apply (globalWinnerLabel_eq_some_iff reentryBlocks.flatten 5 reentryStrong.kappa).mpr
    refine ⟨reentryStrong, ?_, rfl⟩
    unfold globalLocalWins
    decide
  · apply (globalWinnerLabel_eq_some_iff reentryBlocks.flatten 7 reentryWeak.kappa).mpr
    refine ⟨reentryWeak, ?_, rfl⟩
    unfold globalLocalWins
    decide

/-- The unconditional global interval/no-re-entry claim is false. -/
theorem crossBlock_identity_not_interval :
    ¬ Phase12b.IsInterval (fun t => globalLocalWins reentryBlocks.flatten reentryWeak t) := by
  intro h
  have h3 : globalLocalWins reentryBlocks.flatten reentryWeak 3 := by
    unfold globalLocalWins
    decide
  have h7 : globalLocalWins reentryBlocks.flatten reentryWeak 7 := by
    unfold globalLocalWins
    decide
  have h5 : globalLocalWins reentryBlocks.flatten reentryWeak 5 :=
    h 3 h3 7 h7 5 (by omega) (by omega)
  have h5not : ¬ globalLocalWins reentryBlocks.flatten reentryWeak 5 := by
    unfold globalLocalWins
    decide
  exact h5not h5

end BlockWinnerNoReentry

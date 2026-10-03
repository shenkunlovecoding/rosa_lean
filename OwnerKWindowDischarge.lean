import OwnerKBaselineEnvelope

/-!
## Discharging the finite local data in `HasRosaKWindow`

This file does not change the existing ROSA interfaces.  It packages the parts
of `BlockWinnerNoReentry.HasRosaKWindow` that are consequences of a concrete
fixed-owner bridge list.

The remaining local input is a *single deletion-window anchor*: the bridge wins
the deletion baseline at `d`, and (if `d` is not the birth) fails to win it just
before `d`.  `rosa_trim_closed` then propagates these endpoint facts to the two
threshold obligations in `HasRosaKWindow`.

All shadow-reach and finite expiry-maximum data are constructed here.
-/

namespace OwnerKWindowDischarge

open Route RosBridge CommonBirth KDeleteAbstract KDeleteROSA
open OwnerBridges BlockWinnerNoReentry OwnerKBaselineEnvelope

variable {α : Type} [DecidableEq α]

/-! ### Left-context bounds -/

/-- The guarded left context never exceeds the Q-birth coordinate. -/
theorem leftCtx_le_left (q k : Nat → α) (p u : Nat) :
    Repair.leftCtx q k p u ≤ p := by
  unfold Repair.leftCtx
  split
  · omega
  · rename_i hguard
    have h := Lcs.lcsLen_le_bound q k (p - 1) (u - 1)
    omega

/-- The guarded left context never exceeds the K-owner coordinate. -/
theorem leftCtx_le_owner (q k : Nat → α) (p u : Nat) :
    Repair.leftCtx q k p u ≤ u := by
  unfold Repair.leftCtx
  split
  · omega
  · rename_i hguard
    have h := Lcs.lcsLen_le_bound q k (p - 1) (u - 1)
    omega

/-- The guarded left context is bounded by the unguarded LCSuffix at a causal
centre.  This is the last field needed for `RealisedK`. -/
theorem leftCtx_le_lcsLen (q k : Nat → α) (p u : Nat) :
    Repair.leftCtx q k p u ≤ Lcs.lcsLen q k (p - 1) (u - 1) := by
  unfold Repair.leftCtx
  split
  · omega
  · omega

/-- A literal `mkBridge` at a causal centre is realised: at positive centres its
left context is exactly the unguarded LCSuffix, while the zero-owner boundary
case has left context `0`. -/
theorem realisedK_mkBridge_of_lt {q k : Nat → α} {Tq Tk p u : Nat}
    (hup : u < p) :
    RealisedK q k u (mkBridge q k Tq Tk p u) := by
  refine ⟨rfl, hup, leftCtx_le_left q k p u, leftCtx_le_owner q k p u,
    leftCtx_le_lcsLen q k p u⟩

/-- Every element of the concrete fixed-owner bridge list is realised, including
the owner-boundary cases `u = c` and `u = d`. -/
theorem realisedK_of_mem_kOwnerBridges {q k : Nat → α}
    {Tq Tk a b c d u : Nat} {x : Bridge}
    (hx : x ∈ kOwnerBridges q k Tq Tk a b c d u) :
    RealisedK q k u x := by
  obtain ⟨-, -, p, -, -, hup, rfl⟩ := mem_kOwnerBridges.mp hx
  exact realisedK_mkBridge_of_lt (q := q) (k := k) (Tq := Tq) (Tk := Tk) hup

/-! ### Shadow reach from `κ` -/

/-- Strictly better `κ` already has its shadow start no later than the birth of
the bridge it beats.  Same-owner is not needed for this arithmetic fact. -/
theorem shadowStart_le_birth_of_klexLT {c b : Bridge}
    (hbetter : klexLT c.kappa b.kappa) :
    c.shadowStart ≤ (b.p : Int) := by
  have hle : klexLE c.kappa b.kappa := hbetter.1
  rcases hle with hlt | ⟨heq, -⟩
  · change (c.p : Int) - (c.L : Int) ≤ (b.p : Int)
    unfold Bridge.kappa at hlt
    omega
  · change (c.p : Int) - (c.L : Int) ≤ (b.p : Int)
    unfold Bridge.kappa at heq
    omega

/-! ### Finite expiry maximum -/

/-- The strictly-better members of a fixed-owner bridge list. -/
def betterBridges (bs : List Bridge) (b : Bridge) : List Bridge :=
  bs.filter (fun c => decide (klexLT c.kappa b.kappa))

/-- The largest expiry among strictly-better bridges, seeded at zero. -/
def expiryBound (bs : List Bridge) (b : Bridge) : Nat :=
  (betterBridges bs b).foldr (fun c acc => max c.death acc) 0

private theorem death_le_foldr_max {l : List Bridge} {c : Bridge} {seed : Nat}
    (hc : c ∈ l) :
    c.death ≤ l.foldr (fun x acc => max x.death acc) seed := by
  induction l with
  | nil => simp at hc
  | cons x xs ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hc) (Nat.le_max_right _ _)

private theorem exists_death_eq_foldr_max {l : List Bridge} (hne : l ≠ []) :
    ∃ c ∈ l, c.death = l.foldr (fun x acc => max x.death acc) 0 := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    rw [List.foldr_cons]
    by_cases hxs : xs = []
    · subst xs
      refine ⟨x, by simp, ?_⟩
      simp
    · obtain ⟨c, hc, hcdeath⟩ := ih hxs
      by_cases hle : x.death ≤ xs.foldr (fun x acc => max x.death acc) 0
      · refine ⟨c, by simp [hc], ?_⟩
        rw [hcdeath]
        exact (Nat.max_eq_right hle).symm
      · have hle' : xs.foldr (fun x acc => max x.death acc) 0 ≤ x.death := by
          omega
        refine ⟨x, by simp, ?_⟩
        exact (Nat.max_eq_left hle').symm

/-- The finite maximum bounds every strictly-better expiry. -/
theorem death_le_expiryBound {bs : List Bridge} {b c : Bridge}
    (hc : c ∈ bs) (hbetter : klexLT c.kappa b.kappa) :
    c.death ≤ expiryBound bs b := by
  unfold expiryBound betterBridges
  apply death_le_foldr_max
  rw [List.mem_filter]
  exact ⟨hc, by simp [hbetter]⟩

/-- The finite maximum is attained, or is below the birth when there is no
strictly-better bridge.  The explicit fallback is exactly the only edge case:
`b.p = 0` with an empty better-list. -/
theorem expiryBound_matches_or_lt_birth {bs : List Bridge} {b : Bridge}
    (hsep : 0 < b.p ∨ ∃ c ∈ bs, klexLT c.kappa b.kappa) :
    expiryBound bs b < b.p ∨
      ∃ c ∈ bs, klexLT c.kappa b.kappa ∧ c.death = expiryBound bs b := by
  by_cases hlt : expiryBound bs b < b.p
  · exact Or.inl hlt
  · right
    have hne : betterBridges bs b ≠ [] := by
      intro hempty
      rcases hsep with hbirth | ⟨c, hc, hbetter⟩
      · have hzero : expiryBound bs b = 0 := by simp [expiryBound, hempty]
        omega
      · have hmem : c ∈ betterBridges bs b := by
          rw [betterBridges, List.mem_filter]
          exact ⟨hc, by simp [hbetter]⟩
        simp [hempty] at hmem
    obtain ⟨c, hc, hcdeath⟩ := exists_death_eq_foldr_max hne
    have hcbs : c ∈ bs := (List.mem_filter.mp hc).1
    have hbetter : klexLT c.kappa b.kappa := by
      exact of_decide_eq_true (List.mem_filter.mp hc).2
    exact ⟨c, hcbs, hbetter, hcdeath⟩

/-! ### One-point deletion threshold -/

/-- The only deletion-threshold data not implied by the finite bridge list:
a canonical first-win anchor `d`.  The upper active bound `d ≤ death+1` merely
handles the vacuous case in which the bridge never wins. -/
def DeletionWindowAnchor (D : KDeleteFamily) (b : Bridge) (d : Nat) : Prop :=
  b.p ≤ d ∧ d ≤ b.death + 1 ∧
    (d ≤ b.death → D.Beats b d) ∧
    (b.p < d → ¬ D.Beats b (d - 1))

/-- `Beats` is monotone while the bridge is active, by trim-closure. -/
theorem beats_monotone_between {D : KDeleteFamily} (htrim : TrimClosed D)
    {b : Bridge} {i j : Nat} (hij : i ≤ j)
    (hi : b.Active i) (hj : b.Active j) (hbeat : D.Beats b i) :
    D.Beats b j := by
  have hmain : ∀ n, i + n ≤ j → D.Beats b (i + n) := by
    intro n
    induction n with
    | zero => intro _; simpa using hbeat
    | succ n ih =>
        intro hn
        have hn' : i + n ≤ j := by omega
        have hip : b.p ≤ i := hi.1
        have hid : i ≤ b.p + b.R := hi.2
        have hjd : j ≤ b.p + b.R := hj.2
        have hact : b.Active (i + n) := ⟨by omega, by omega⟩
        have hact' : b.Active (i + n + 1) := ⟨by omega, by omega⟩
        exact KDeleteAbstract.beats_delete_monotone htrim hact hact' (ih hn')
  have hj' : j = i + (j - i) := by omega
  rw [hj']
  exact hmain (j - i) (by omega)

/-- Failure later and monotonicity imply failure earlier (within the active
lifetime). -/
theorem not_beats_of_not_beats_later {D : KDeleteFamily} (htrim : TrimClosed D)
    {b : Bridge} {i j : Nat} (hij : i ≤ j)
    (hi : b.Active i) (hj : b.Active j) (hnot : ¬ D.Beats b j) :
    ¬ D.Beats b i := by
  intro hbeat
  exact hnot (beats_monotone_between htrim hij hi hj hbeat)

/-- A one-point anchor automatically gives the two threshold obligations in
`HasRosaKWindow`. -/
theorem deletionWindowBounds_of_anchor {D : KDeleteFamily} {b : Bridge} {d : Nat}
    (htrim : TrimClosed D) (hanchor : DeletionWindowAnchor D b d) :
    (∀ t, b.p ≤ t → t < d → ¬ D.Beats b t) ∧
      (∀ t, d ≤ t → t ≤ b.death → D.Beats b t) := by
  rcases hanchor with ⟨hpd, hdsucc, hbeat_d, hfail_before⟩
  unfold Bridge.death at hdsucc ⊢
  constructor
  · intro t hpt htd
    by_cases hdp : d ≤ b.p
    · omega
    · have hp_lt_d : b.p < d := by omega
      have hnot : ¬ D.Beats b (d - 1) := hfail_before hp_lt_d
      have htd' : t ≤ d - 1 := by omega
      have hact_t : b.Active t := ⟨hpt, by omega⟩
      have hact_last : b.Active (d - 1) := ⟨by omega, by omega⟩
      exact not_beats_of_not_beats_later htrim htd' hact_t hact_last hnot
  · intro t hdt htd
    have hddeath : d ≤ b.death := Nat.le_trans hdt htd
    have hdbeat : D.Beats b d := hbeat_d hddeath
    have hact_d : b.Active d := ⟨hpd, hddeath⟩
    have hact_t : b.Active t := ⟨by omega, htd⟩
    exact beats_monotone_between htrim hdt hact_d hact_t hdbeat

/-! ### Construct `HasRosaKWindow` -/

/-- Construct the full `HasRosaKWindow` from concrete realisability plus one
one-point deletion anchor.  Shadow reach and the finite expiry maximum are
discharged internally. -/
theorem hasRosaKWindow_of_realisedK_anchor {q k : Nat → α} {u d : Nat}
    {bs : List Bridge} {b : Bridge}
    (hreal : ∀ c ∈ bs, klexLT c.kappa b.kappa → RealisedK q k u c)
    (hanchor : DeletionWindowAnchor (rosaKDelete q k u) b d)
    (hsep : 0 < b.p ∨ ∃ c ∈ bs, klexLT c.kappa b.kappa) :
    HasRosaKWindow q k u bs b := by
  let M := expiryBound bs b
  have hbounds := deletionWindowBounds_of_anchor (rosa_trim_closed q k u) hanchor
  refine ⟨d, M, hreal, ?_, hbounds.1, hbounds.2, ?_, ?_⟩
  · intro c hc hbetter
    exact shadowStart_le_birth_of_klexLT hbetter
  · intro c hc hbetter
    exact death_le_expiryBound hc hbetter
  · exact expiryBound_matches_or_lt_birth hsep

/-- The finite-list form of the preceding constructor.  A list member of
`kOwnerBridges` is automatically `RealisedK`, so only the threshold anchor is
external.  In particular, owner boundaries and left-context bounds need no extra
hypotheses. -/
theorem hasRosaKWindow_of_mem_kOwnerBridges {q k : Nat → α}
    {Tq Tk a b c d u : Nat} {x : Bridge} {δ : Nat}
    (hx : x ∈ kOwnerBridges q k Tq Tk a b c d u)
    (hanchor : DeletionWindowAnchor (rosaKDelete q k u) x δ) :
    HasRosaKWindow q k u (kOwnerBridges q k Tq Tk a b c d u) x := by
  apply hasRosaKWindow_of_realisedK_anchor
    (hreal := fun y hy _ => realisedK_of_mem_kOwnerBridges (q := q) (k := k) hy)
    (hanchor := hanchor)
  · left
    have hrealx := realisedK_of_mem_kOwnerBridges (q := q) (k := k) hx
    exact Nat.lt_of_le_of_lt (Nat.zero_le x.u) hrealx.2.1

/-! ### Reduced interval wrappers -/

/-- Reduced-assumption version of
`fixedKOwner_effectiveWinner_isInterval_of_window`. -/
theorem fixedKOwner_effectiveWinner_isInterval_of_realisedK_anchor
    {q k : Nat → α} {u d : Nat} {bs : List Bridge} {b : Bridge}
    (hreal : ∀ c ∈ bs, klexLT c.kappa b.kappa → RealisedK q k u c)
    (hanchor : DeletionWindowAnchor (rosaKDelete q k u) b d)
    (hsep : 0 < b.p ∨ ∃ c ∈ bs, klexLT c.kappa b.kappa) :
    Phase12b.IsInterval
      (fun t => EffectiveKWinner (rosaKDelete q k u) u bs b t) := by
  exact OwnerKBaselineEnvelope.fixedKOwner_effectiveWinner_isInterval_of_window
    (q := q) (k := k) (u := u) (bs := bs) (b := b)
    (hasRosaKWindow_of_realisedK_anchor hreal hanchor hsep)

/-- Concrete fixed-owner wrapper: only the one-point deletion anchor remains
external.  The bridge is taken from the actual `kOwnerBridges` list. -/
theorem fixedKOwner_effectiveWinner_isInterval_of_kOwnerBridges
    {q k : Nat → α} {Tq Tk a b c d u : Nat} {x : Bridge} {δ : Nat}
    (hx : x ∈ kOwnerBridges q k Tq Tk a b c d u)
    (hanchor : DeletionWindowAnchor (rosaKDelete q k u) x δ) :
    Phase12b.IsInterval
      (fun t => EffectiveKWinner (rosaKDelete q k u) u
        (kOwnerBridges q k Tq Tk a b c d u) x t) := by
  exact OwnerKBaselineEnvelope.fixedKOwner_effectiveWinner_isInterval_of_window
    (q := q) (k := k) (u := u)
    (bs := kOwnerBridges q k Tq Tk a b c d u) (b := x)
    (hasRosaKWindow_of_mem_kOwnerBridges hx hanchor)

/-- The same reduction at the canonical identity-class level.  Every concrete
bridge needs only an existential one-point deletion anchor. -/
theorem fixedKOwner_canonicalWinner_isInterval_of_kOwnerBridges
    {q k : Nat → α} {Tq Tk a b c d u : Nat} (κ : Int × Int)
    (hanchor : ∀ x ∈ kOwnerBridges q k Tq Tk a b c d u,
      ∃ δ, DeletionWindowAnchor (rosaKDelete q k u) x δ) :
    Phase12b.IsInterval (fun t =>
      kWinnerLabel (rosaKDelete q k u) u
        (kOwnerBridges q k Tq Tk a b c d u) t = some κ) := by
  apply OwnerKBaselineEnvelope.fixedKOwner_canonicalWinner_isInterval_of_windows
  intro x hx
  obtain ⟨δ, hδ⟩ := hanchor x hx
  exact hasRosaKWindow_of_mem_kOwnerBridges hx hδ

end OwnerKWindowDischarge

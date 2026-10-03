import Std
import RosBridge

/-!
## Exact ROSA credit — §3 of `ROSA_Credit_New_Results`

*"Q 修复包络只需‘排序 + 到期纪录’"* — for a fixed `(Q, p, bit)` all repair bridges
share the birth instant `p`.  Their route priority

`(L + 1 + t - p, u + t - p)`

is a **time-independent** ordering of the pair `(L, u)` (both coordinates shift by
the same `t - p`), so sorting the candidates once by descending priority and then
sweeping with a single "covered up to `e`" cursor

```text
e = p - 1
for bridge in descending_priority:
    if bridge.death > e:
        emit [e + 1, bridge.death] with this bridge
        e = bridge.death
```

produces exactly the Q repair envelope: the emitted segments tile
`[p, max death]`, and on each segment the labelling bridge is the ROSA winner
among the *live* candidates.

This file proves that sweep correct on top of the existing
`RosBridge.bridge_kappa_const` (priority is constant along a lifetime) and
`RosBridge.route_rle_iff_kappa`.  It is the algorithmic counterpart of
`CommonBirth.common_birth_winner_iff`, which gives the winner *interval*
`[max(p, M_b+1), e_b]` of a common-birth candidate.
-/

namespace QEExpiry

open RosBridge

/-! ### Ordering and scan -/

/-- Descending priority order of a candidate list at the common birth instant
`p`: every earlier bridge beats every later one in the ROSA route order
(`Route.rle y x` means `x` is the better route). -/
def SortedDesc (p : Nat) (bs : List Bridge) : Prop :=
  bs.Pairwise (fun x y => Route.rle (y.routeAt p) (x.routeAt p))

/-- Maximum expiry of a bridge list (`0` for the empty list). -/
def maxDeath (bs : List Bridge) : Nat := bs.foldr (fun b acc => max b.death acc) 0

/-- The record-expiry sweep.  `cov` is the latest already-covered instant
(initially `p - 1`); a bridge that outlives `cov` emits `[cov+1, b.death]`. -/
def scanAll : List Bridge → Nat → List (Nat × Nat × Bridge) × Nat
  | [], cov => ([], cov)
  | b :: bs, cov =>
      if _ : cov < b.death then
        ((cov + 1, b.death, b) :: (scanAll bs b.death).1, (scanAll bs b.death).2)
      else
        scanAll bs cov

/-- The public sweep: candidates share the birth instant `p`, coverage starts at
`p - 1`. -/
def qExpirySkyline (p : Nat) (bs : List Bridge) : List (Nat × Nat × Bridge) :=
  (scanAll bs (p - 1)).1

/-! ### Priority is time-independent -/

/-- **§3, ordering lemma.**  Two bridges with the same birth instant compare the
same way at every common instant of their lifetimes (`bridge_kappa_const`). -/
theorem bridge_rle_const {b c : Bridge} {p t : Nat}
    (_hb : b.p = p) (_hc : c.p = p) (_ht : p ≤ t) (hab : b.Active t) (hac : c.Active t) :
    Route.rle (b.routeAt t) (c.routeAt t) ↔ Route.rle (b.routeAt p) (c.routeAt p) := by
  have habp : b.Active p := by
    rw [Bridge.Active, _hb]
    exact ⟨Nat.le_refl p, Nat.le_add_right p b.R⟩
  have hacp : c.Active p := by
    rw [Bridge.Active, _hc]
    exact ⟨Nat.le_refl p, Nat.le_add_right p c.R⟩
  have h1 : Route.rle (b.routeAt t) (c.routeAt t) ↔ klexLE c.kappa b.kappa := by
    rw [route_rle_iff_kappa t, bridge_kappa_const b t hab, bridge_kappa_const c t hac]
  have h2 : Route.rle (b.routeAt p) (c.routeAt p) ↔ klexLE c.kappa b.kappa := by
    rw [route_rle_iff_kappa p, bridge_kappa_const b p habp, bridge_kappa_const c p hacp]
  rw [h1, h2]

/-! ### The winner predicate -/

/-- `b` is the ROSA winner at `t` among the live bridges of `cs`. -/
def IsMax (cs : List Bridge) (t : Nat) (b : Bridge) : Prop :=
  b ∈ cs ∧ b.Active t ∧ ∀ c ∈ cs, c.Active t → Route.rle (c.routeAt t) (b.routeAt t)

/-! ### Coverage -/

/-- **§3, coverage.**  The sweep's final cursor is `max cov (max death)`, so the
emitted segments tile `[p, max death]` when started at `cov = p - 1`. -/
theorem scanAll_covered (bs : List Bridge) (cov : Nat) :
    (scanAll bs cov).2 = max cov (maxDeath bs) := by
  induction bs generalizing cov with
  | nil => simp [scanAll, maxDeath]
  | cons b bs ih =>
    rw [scanAll]
    by_cases h : cov < b.death
    · rw [dif_pos h, ih b.death]
      simp only [maxDeath, List.foldr_cons]
      omega
    · rw [dif_neg h, ih cov]
      simp only [maxDeath, List.foldr_cons]
      omega

/-- **§3, segment count.**  At most one emitted segment per candidate. -/
theorem scanAll_length_le (bs : List Bridge) (cov : Nat) :
    (scanAll bs cov).1.length ≤ bs.length := by
  induction bs generalizing cov with
  | nil => simp [scanAll]
  | cons b bs ih =>
    rw [scanAll]
    by_cases h : cov < b.death
    · rw [dif_pos h]
      have := ih b.death
      simp only [List.length_cons]
      omega
    · rw [dif_neg h]
      have := ih cov
      simp only [List.length_cons]
      omega

/-! ### Correctness of the labelling -/

/-- **§3, main theorem.**  If `bs` is sorted by descending priority and all its
bridges (as well as the already-swept `pref`, whose expiries are `≤ cov`) share
the birth instant `p`, then every emitted segment `[lo, hi]` is labelled by a
bridge that is the ROSA winner at each of its instants, among `pref ++ bs`. -/
theorem scanAll_spec (bs : List Bridge) (cov p : Nat) (pref : List Bridge)
    (hp : p - 1 ≤ cov)
    (hbirth : ∀ b ∈ bs, b.p = p)
    (hbirthPref : ∀ a ∈ pref, a.p = p)
    (hsortedPref : ∀ a ∈ pref, ∀ b ∈ bs, Route.rle (b.routeAt p) (a.routeAt p))
    (hpw : SortedDesc p bs)
    (hprefDead : ∀ a ∈ pref, a.death ≤ cov) :
    ∀ lo hi b, (lo, hi, b) ∈ (scanAll bs cov).1 →
      b ∈ bs ∧ cov < lo ∧ lo ≤ hi ∧ hi = b.death ∧
        ∀ t, lo ≤ t → t ≤ hi → IsMax (pref ++ bs) t b := by
  induction bs generalizing cov pref with
  | nil => intro lo hi b h; rw [scanAll] at h; simp at h
  | cons b₀ bs ih =>
    intro lo hi b hseg
    rw [scanAll] at hseg
    have hbirth₀ : b₀.p = p := hbirth b₀ (by simp)
    have hbirthTail : ∀ b ∈ bs, b.p = p := fun b hb => hbirth b (by simp [hb])
    rw [SortedDesc, List.pairwise_cons] at hpw
    obtain ⟨hpwhead, hpwtail⟩ := hpw
    by_cases h : cov < b₀.death
    · rw [dif_pos h] at hseg
      rcases List.mem_cons.mp hseg with hhead | htail
      · -- the newly emitted segment is labelled by `b₀`
        simp only [Prod.mk.injEq] at hhead
        obtain ⟨hlo, hhi, hb⟩ := hhead
        cases hb
        refine ⟨by simp, by omega, by omega, by omega, ?_⟩
        intro t htlo hthi
        have hht : p ≤ t := by omega
        have hact : b₀.Active t := by
          have h2 : t ≤ b₀.death := by omega
          have h2' : t ≤ b₀.p + b₀.R := h2
          rw [Bridge.Active, hbirth₀]
          exact ⟨hht, by rw [← hbirth₀]; exact h2'⟩
        refine ⟨by simp, hact, ?_⟩
        intro c hc hcact
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · -- `c` was already swept: its expiry is below the emitted lower bound
          have hcd : c.p + c.R ≤ cov := hprefDead c hc
          rw [Bridge.Active] at hcact
          omega
        · rw [List.mem_cons] at hc
          rcases hc with rfl | hcbs
          · exact Route.rle_refl _
          · have hsort : Route.rle (c.routeAt p) (b₀.routeAt p) := hpwhead c hcbs
            have hcp : c.p = p := hbirth c (by simp [hcbs])
            exact (bridge_rle_const hcp hbirth₀ hht hcact hact).mpr hsort
      · -- a later segment: recurse with `pref ++ [b₀]`
        have hbirthPref' : ∀ a ∈ pref ++ [b₀], a.p = p := by
          intro a ha
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact hbirthPref a ha
          · rw [List.mem_singleton] at ha; subst ha; exact hbirth₀
        have hsortedPref' : ∀ a ∈ pref ++ [b₀], ∀ b ∈ bs,
            Route.rle (b.routeAt p) (a.routeAt p) := by
          intro a ha b hb
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact hsortedPref a ha b (by simp [hb])
          · rw [List.mem_singleton] at ha; subst ha
            exact hpwhead b hb
        have hprefDead' : ∀ a ∈ pref ++ [b₀], a.death ≤ b₀.death := by
          intro a ha
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hprefDead a ha) h)
          · rw [List.mem_singleton] at ha; subst ha; exact Nat.le_refl _
        have hrec := ih b₀.death (pref ++ [b₀]) (by omega) hbirthTail hbirthPref'
          hsortedPref' hpwtail hprefDead' lo hi b htail
        obtain ⟨hmem, hlt, hle, heq, himax⟩ := hrec
        refine ⟨by simp [hmem], by omega, hle, heq, ?_⟩
        intro t htlo hthi
        have := himax t htlo hthi
        rwa [List.append_assoc, List.singleton_append] at this
    · -- `b₀` never wins: recurse with the same cursor and `pref ++ [b₀]`
      rw [dif_neg h] at hseg
      have hbirthPref' : ∀ a ∈ pref ++ [b₀], a.p = p := by
        intro a ha
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · exact hbirthPref a ha
        · rw [List.mem_singleton] at ha; subst ha; exact hbirth₀
      have hsortedPref' : ∀ a ∈ pref ++ [b₀], ∀ b ∈ bs,
          Route.rle (b.routeAt p) (a.routeAt p) := by
        intro a ha b hb
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · exact hsortedPref a ha b (by simp [hb])
        · rw [List.mem_singleton] at ha; subst ha
          exact hpwhead b hb
      have hprefDead' : ∀ a ∈ pref ++ [b₀], a.death ≤ cov := by
        intro a ha
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · exact hprefDead a ha
        · rw [List.mem_singleton] at ha; subst ha; omega
      have hrec := ih cov (pref ++ [b₀]) hp hbirthTail hbirthPref'
        hsortedPref' hpwtail hprefDead' lo hi b hseg
      obtain ⟨hmem, hlt, hle, heq, himax⟩ := hrec
      refine ⟨by simp [hmem], hlt, hle, heq, ?_⟩
      intro t htlo hthi
      have := himax t htlo hthi
      rwa [List.append_assoc, List.singleton_append] at this

/-! ### Public statements -/

/-- **§3 (public form).**  Sorting the common-birth candidates by descending
priority and sweeping with the expiry record produces segments on which the
labelling bridge is the ROSA winner among all live candidates. -/
theorem qExpirySkyline_spec (bs : List Bridge) (p : Nat)
    (hbirth : ∀ b ∈ bs, b.p = p) (hpw : SortedDesc p bs) :
    ∀ lo hi b, (lo, hi, b) ∈ qExpirySkyline p bs →
      b ∈ bs ∧ p - 1 < lo ∧ lo ≤ hi ∧ hi = b.death ∧
        ∀ t, lo ≤ t → t ≤ hi → IsMax bs t b := by
  intro lo hi b hseg
  have h := scanAll_spec bs (p - 1) p [] (Nat.le_refl _) hbirth
    (by intro a ha; simp at ha) (by intro a ha; simp at ha) hpw
    (by intro a ha; simp at ha) lo hi b hseg
  obtain ⟨hmem, hlt, hle, heq, himax⟩ := h
  refine ⟨hmem, hlt, hle, heq, ?_⟩
  intro t htlo hthi
  have := himax t htlo hthi
  rwa [List.nil_append] at this

/-- **§3 (coverage form).**  The sweep starting at `p - 1` covers up to the last
expiry. -/
theorem qExpirySkyline_covered (bs : List Bridge) (p : Nat) :
    (scanAll bs (p - 1)).2 = max (p - 1) (maxDeath bs) :=
  scanAll_covered bs (p - 1)

/-- **§3 (segment count).**  The envelope has at most one segment per candidate. -/
theorem qExpirySkyline_length_le (bs : List Bridge) (p : Nat) :
    (qExpirySkyline p bs).length ≤ bs.length :=
  scanAll_length_le bs (p - 1)

end QEExpiry

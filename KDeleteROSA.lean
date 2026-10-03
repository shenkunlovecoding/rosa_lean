import Std
import Lcs
import Repair
import RosBridge
import KDeleteAbstract
import KSkyline

/-!
## Phase H (2) — `KDeleteROSA.lean`: discharging `Dᵤ` from the string layer

`rosaKDelete q k u` is the deletion family "delete `k[u]`": the suffix-match routes
of `q[0..t]` whose matched `k`-range avoids position `u`.  From it we *derive* the
two abstract properties `TrimClosed` and `HasPrebirthShadow`, so
`KSkyline.k_suffix_winner_iff` applies with no further assumptions.
-/

namespace KDeleteROSA
open Route Lcs Repair RosBridge CommonBirth KDeleteAbstract

variable {α : Type} [DecidableEq α]

/-- `k`-suffix-match routes of `q[0..t]` whose matched range avoids `u`
(i.e. do not use `k[u]`) — the "delete `k[u]`" candidates of §11.

The endpoint runs over `ep < t`, matching `LCSuffix(e<t)` and
`CutArith.bruteKCut`.  In particular, the current query endpoint `e = t` is not
part of the deletion baseline. -/
def rosaCand (q k : Nat → α) (u t : Nat) : List Route :=
  List.flatMap (fun r =>
      List.filterMap (fun (l : Nat) =>
          if 1 ≤ l ∧ (r < u ∨ u < r + 1 - l) then
            some (⟨(l : Int), (r : Int)⟩ : Route) else none)
        (List.range (lcsLen q k t r + 1)))
    (List.range t)

/-- The ROSA deletion family `𝒟ᵤ`. -/
def rosaKDelete (q k : Nat → α) (u : Nat) : KDeleteFamily := ⟨fun t => rosaCand q k u t⟩

/-- Backward membership for `rosaCand`.

The boundary hypothesis is deliberately stated as `u < ep + 1 - l`, the
underflow-safe natural-number form of the interval's left endpoint.  Compared
with the old `u < ep - l + 1` condition, this hypothesis is stronger exactly in
the former underflow case `l = ep + 1 ∧ u = 0`; for every candidate the only
possible disagreement is that exceptional case. -/
theorem mem_rosaCand_bwd {q k : Nat → α} {u t l ep : Nat}
    (hl1 : 1 ≤ l) (hle : l ≤ lcsLen q k t ep) (hep : ep < t)
    (hav : ep < u ∨ u < ep + 1 - l) :
    (⟨(l : Int), (ep : Int)⟩ : Route) ∈ rosaCand q k u t := by
  rw [rosaCand, List.mem_flatMap]
  refine ⟨ep, by rw [List.mem_range]; exact hep, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨l, by rw [List.mem_range]; omega, ?_⟩
  simp only [hl1, hav, and_self, if_true]

/-- Forward membership for `rosaCand`.

The extracted avoidance condition is the same underflow-safe proposition as
the backward theorem.  It is stronger than the old underflow-prone conclusion
exactly when `l = ep + 1 ∧ u = 0`, the case that had incorrectly admitted the
singleton match on `k[0]`. -/
theorem mem_rosaCand_fwd {q k : Nat → α} {u t : Nat} {x : Route}
    (h : x ∈ rosaCand q k u t) :
    ∃ l ep : Nat, 1 ≤ l ∧ l ≤ lcsLen q k t ep ∧ ep < t ∧
      (ep < u ∨ u < ep + 1 - l) ∧ x = (⟨(l : Int), (ep : Int)⟩ : Route) := by
  rw [rosaCand, List.mem_flatMap] at h
  obtain ⟨ep, hep, hx⟩ := h
  rw [List.mem_range] at hep
  rw [List.mem_filterMap] at hx
  obtain ⟨l, hl, hlx⟩ := hx
  rw [List.mem_range] at hl
  by_cases hc : 1 ≤ l ∧ (ep < u ∨ u < ep + 1 - l)
  · rw [if_pos hc, Option.some.injEq] at hlx
    exact ⟨l, ep, hc.1, by omega, hep, hc.2, hlx.symm⟩
  · rw [if_neg hc] at hlx
    simp at hlx

/-- Regression theorem for the corrected boundary semantics: the length-one
match `[0,0]` on `k[0]` is not a candidate when deleting `k[0]`.  The old
truncated expression admitted this route because the left endpoint was computed
as `0 - 1 + 1 = 1`, making the false avoidance test `0 < 1` succeed. -/
theorem singleton_zero_not_mem_rosaCand (q k : Nat → α) :
    (⟨(1 : Int), (0 : Int)⟩ : Route) ∉ rosaCand q k 0 0 := by
  intro h
  obtain ⟨l, ep, hl1, _hle, hep, hav, _hx⟩ := mem_rosaCand_fwd h
  omega

/-- Domain regression: no candidate may use the current query endpoint `t`.
This is the general form of `singleton_zero_not_mem_rosaCand`. -/
theorem self_endpoint_not_mem_rosaCand (q k : Nat → α) (u t l : Nat) :
    (⟨(l : Int), (t : Int)⟩ : Route) ∉ rosaCand q k u t := by
  intro h
  obtain ⟨_l', ep, _hl1, _hle, hep, _hav, hx⟩ := mem_rosaCand_fwd h
  have hep_eq : ep = t := by
    have := congrArg Route.endpoint hx
    dsimp at this
    omega
  omega

/-- **Discharge of `TrimClosed`** (§12): dropping the last character keeps a
`delete-k[u]` candidate. -/
theorem rosa_trim_closed (q k : Nat → α) (u : Nat) : TrimClosed (rosaKDelete q k u) := by
  intro t r hr hl2
  obtain ⟨l, ep, hl1, hle, hep, hav, rfl⟩ := mem_rosaCand_fwd hr
  dsimp only at hl2
  have hl2' : 2 ≤ l := by omega
  have hep1 : 1 ≤ ep := by
    have h3 : 2 ≤ ep + 1 :=
      Nat.le_trans hl2' (Nat.le_trans hle
        (Nat.le_trans (lcsLen_le_bound q k (t + 1) ep) (Nat.min_le_right _ _)))
    omega
  have hse : SuffixEq q k (t + 1) ep l :=
    suffixEq_mono (lcsLen_spec q k (t + 1) ep) hle
  have hse' : SuffixEq q k t (ep - 1) (l - 1) := by
    obtain ⟨h1, h2, h3⟩ := hse
    refine ⟨by omega, by omega, ?_⟩
    intro h' hh'
    rw [List.mem_range] at hh'
    have h3' := h3 (h' + 1) (List.mem_range.mpr (by omega))
    have e1 : t - h' = (t + 1) - (h' + 1) := by omega
    have e2 : (ep - 1) - h' = ep - (h' + 1) := by omega
    rw [e1, e2]
    exact h3'
  have hle' : l - 1 ≤ lcsLen q k t (ep - 1) := lcsLen_greatest hse'
  have hav' : ep - 1 < u ∨ u < ep - 1 + 1 - (l - 1) := by omega
  have hmem : (⟨((l - 1 : Nat) : Int), ((ep - 1 : Nat) : Int)⟩ : Route)
      ∈ (rosaKDelete q k u).cand t :=
    mem_rosaCand_bwd (by omega) hle' (by omega) hav'
  have htrim : trim (⟨(l : Int), (ep : Int)⟩ : Route)
      = (⟨((l - 1 : Nat) : Int), ((ep - 1 : Nat) : Int)⟩ : Route) := by
    unfold trim
    dsimp only
    rw [Route.mk.injEq]
    exact ⟨by omega, by omega⟩
  rw [htrim]
  exact hmem

/-- **Discharge of `HasPrebirthShadow`** (§11).  For a bridge `c` realised by `q,k`
with K-owner `u`, the left-context route (and its trims) sit in `𝒟ᵤ`, all carrying
`κ_c`: `c`'s priority is already present before its birth. -/
theorem rosa_has_prebirth_shadow (q k : Nat → α) (u : Nat) (c : Bridge)
    (hu : c.u = u) (hup : c.u < c.p) (hLp : c.L ≤ c.p) (hLu : c.L ≤ c.u)
    (hLc : c.L ≤ lcsLen q k (c.p - 1) (c.u - 1)) :
    HasPrebirthShadow (rosaKDelete q k u) c := by
  intro t hts htc
  have hpt : c.p - c.L ≤ t := by
    have := hts
    unfold Bridge.shadowStart at this
    omega
  have hpc : c.p ≤ t + c.L := by omega
  have hpu : c.p ≤ t + c.u := by omega
  have hlt : t < c.p := htc
  have hse : SuffixEq q k (c.p - 1) (c.u - 1) c.L :=
    suffixEq_mono (lcsLen_spec q k (c.p - 1) (c.u - 1)) hLc
  -- the witness route
  refine ⟨(⟨((t + c.L - c.p + 1 : Nat) : Int), ((t + c.u - c.p : Nat) : Int)⟩ : Route),
    ?_, ?_⟩
  · -- membership: the shadow route is (a prefix of) the left context
    refine mem_rosaCand_bwd (q := q) (k := k) (u := u) (t := t)
      (l := t + c.L - c.p + 1) (ep := t + c.u - c.p) (by omega) ?_ (by omega) ?_
    · apply lcsLen_greatest
      obtain ⟨hs1, hs2, hs3⟩ := hse
      refine ⟨by omega, by omega, ?_⟩
      intro h' hh'
      rw [List.mem_range] at hh'
      have h3' := hs3 (c.p - 1 - t + h') (List.mem_range.mpr (by omega))
      have e1 : t - h' = (c.p - 1) - (c.p - 1 - t + h') := by omega
      have e2 : (t + c.u - c.p) - h' = (c.u - 1) - (c.p - 1 - t + h') := by omega
      rw [e1, e2]
      exact h3'
    · -- the range avoids `u`
      omega
  · -- κ is preserved
    unfold routeKappa Bridge.kappa
    apply Prod.ext <;> simp only <;> omega

/-- A bridge realised by `q,k` under K-owner `u` (a genuine causal one-bit centre). -/
def RealisedK (q k : Nat → α) (u : Nat) (c : Bridge) : Prop :=
  c.u = u ∧ c.u < c.p ∧ c.L ≤ c.p ∧ c.L ≤ c.u ∧ c.L ≤ lcsLen q k (c.p - 1) (c.u - 1)

/-- **Discharged K-suffix theorem.**  `KSkyline.k_suffix_winner_iff` with the two
abstract predicates **discharged** from the string layer: `TrimClosed` by
`rosa_trim_closed` and `HasPrebirthShadow` by `rosa_has_prebirth_shadow`. -/
theorem rosa_k_suffix_winner_iff {q k : Nat → α} {u : Nat} {others : List Bridge} {b : Bridge}
    (hreal : ∀ c ∈ others, klexLT c.kappa b.kappa → RealisedK q k u c)
    (hreach : ∀ c ∈ others, klexLT c.kappa b.kappa → c.shadowStart ≤ (b.p : Int))
    {d : Nat} (hdlow : ∀ t, b.p ≤ t → t < d → ¬ (rosaKDelete q k u).Beats b t)
    (hdhigh : ∀ t, d ≤ t → t ≤ b.death → (rosaKDelete q k u).Beats b t)
    {M : Nat} (hM : ∀ c ∈ others, klexLT c.kappa b.kappa → c.death ≤ M)
    (hMat : M < b.p ∨ ∃ c ∈ others, klexLT c.kappa b.kappa ∧ c.death = M) :
    ∀ t, (b.Active t ∧ (rosaKDelete q k u).Beats b t ∧
        ∀ c ∈ others, c.Active t → ¬ klexLT c.kappa b.kappa)
      ↔ max b.p (max d (M + 1)) ≤ t ∧ t ≤ b.death :=
  KSkyline.k_suffix_winner_iff (rosa_trim_closed q k u)
    (fun c hc hb => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hreal c hc hb
      exact rosa_has_prebirth_shadow q k u c h1 h2 h3 h4 h5)
    hreach hdlow hdhigh hM hMat

end KDeleteROSA

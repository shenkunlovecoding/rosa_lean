import Std
import Route
import RosBridge
import CommonBirth

/-!
## Phase H (new) — step 6/7: abstract `𝒟ᵤ` (`KDeleteAbstract`)

We abstract the K-deletion candidate family `𝒟ᵤ` and **only two structural
properties** — no A/H oracle, no `lcsLen`, no strings:

* `HasPrebirthShadow D c` (§11, **a predicate, not an axiom**): before `c` is
  born, `𝒟` already carries its priority `κ_c`.
* `TrimClosed D` (§12): candidates survive trimming back one character.

Step 6/7 theorems are derived from these; the ROSA string layer is a *separate*
refinement (`rosaKDelete`), so the skyline algebra never sees `q,k`.
-/

namespace KDeleteAbstract
open Route RosBridge CommonBirth

/-- An abstract K-deletion candidate family: at each time `t` a list of routes. -/
structure KDeleteFamily where
  cand : Nat → List Route

namespace KDeleteFamily

/-- The deletion baseline: the best candidate at `t`. -/
def best (D : KDeleteFamily) (t : Nat) : Route := rmaxList (D.cand t)

/-- `b` beats the deletion baseline at `t` (candidate-wise, so no extraction glue). -/
def Beats (D : KDeleteFamily) (b : Bridge) (t : Nat) : Prop :=
  ∀ r ∈ D.cand t, rle r (b.routeAt t)

end KDeleteFamily

open KDeleteFamily

/-- Trim: drop the last character (`ℓ ↓ 1`, `endpoint ↓ 1`). -/
def trim (r : Route) : Route := ⟨r.len - 1, r.endpoint - 1⟩

/-- **`TrimClosed`** (§12): a candidate at `t+1` of length `≥ 2` trims back. -/
def TrimClosed (D : KDeleteFamily) : Prop :=
  ∀ t r, r ∈ D.cand (t + 1) → 2 ≤ r.len → trim r ∈ D.cand t

/-- **`HasPrebirthShadow`** (§11): before `c` is born, `𝒟` carries its priority. -/
def HasPrebirthShadow (D : KDeleteFamily) (c : Bridge) : Prop :=
  ∀ (t : Nat), c.shadowStart ≤ (t : Int) → t < c.birth →
    ∃ r, r ∈ D.cand t ∧ routeKappa t r = c.kappa

/-! ### Pure arithmetic / route lemmas -/

theorem Bridge.routeAt_len (b : Bridge) (t : Nat) :
    (b.routeAt t).len = ((b.L + 1 + (t - b.p) : Nat) : Int) := rfl

theorem rle_len_le {a b : Route} (h : rle a b) : a.len ≤ b.len := by
  unfold rle at h
  rcases h with h | ⟨h, _⟩ <;> omega

/-- Trimming preserves `κ` while shifting the time back by one. -/
theorem trim_kappa (r : Route) (t : Nat) (h : 2 ≤ r.len) :
    routeKappa t (trim r) = routeKappa (t + 1) r := by
  unfold trim routeKappa
  apply Prod.ext <;> simp only <;> omega

/-- An active bridge at `t+1` (with `t ≥ p`) has length `≥ 2`. -/
theorem bridge_len_two {b : Bridge} {t : Nat} (hbt : b.Active t) :
    2 ≤ (b.routeAt (t + 1)).len := by
  rw [Bridge.routeAt_len]
  have : 1 ≤ (t + 1) - b.p := by have := hbt.1; omega
  omega

/-! ### step 7 — `𝒟ᵤ` step-down (a candidate beating `b` at `t+1` beats it at `t`) -/

theorem kdelete_step {D : KDeleteFamily} (htrim : TrimClosed D) {b : Bridge} {t : Nat}
    (hbt : b.Active t) (hbt1 : b.Active (t + 1))
    {r : Route} (hr : r ∈ D.cand (t + 1)) (hrb : rle (b.routeAt (t + 1)) r) :
    ∃ r', r' ∈ D.cand t ∧ rle (b.routeAt t) r' := by
  have hlen2 : 2 ≤ r.len := Int.le_trans (bridge_len_two hbt) (rle_len_le hrb)
  refine ⟨trim r, htrim t r hr hlen2, ?_⟩
  rw [route_rle_iff_kappa, trim_kappa r t hlen2, bridge_kappa_const b t hbt]
  rw [route_rle_iff_kappa, bridge_kappa_const b (t + 1) hbt1] at hrb
  exact hrb

/-- **step 7 — beats-delete monotonicity.**  Once `b` beats the deletion baseline
it keeps beating it (while active).  Derived from `TrimClosed`, not assumed. -/
theorem beats_delete_monotone {D : KDeleteFamily} (htrim : TrimClosed D) {b : Bridge} {t : Nat}
    (hbt : b.Active t) (hbt1 : b.Active (t + 1)) (hbeat : D.Beats b t) :
    D.Beats b (t + 1) := by
  intro r hr
  by_cases hlen : 2 ≤ r.len
  · have h1 : rle (trim r) (b.routeAt t) := hbeat (trim r) (htrim t r hr hlen)
    rw [route_rle_iff_kappa, trim_kappa r t hlen, bridge_kappa_const b t hbt] at h1
    rw [route_rle_iff_kappa, bridge_kappa_const b (t + 1) hbt1]
    exact h1
  · unfold rle
    left
    have := bridge_len_two hbt
    rw [Bridge.routeAt_len] at this ⊢
    omega

/-! ### step 6 — pre-birth shadow ⇒ a future better bridge already blocks -/

/-- The shadow **fails** the deletion baseline for `b`: a strictly-better future
bridge blocks `b` through `D` (strictly not-beats, not just `<= best`). -/
theorem shadow_not_beats {D : KDeleteFamily} {b c : Bridge}
    (hshadow : HasPrebirthShadow D c) (hbetter : klexLT c.kappa b.kappa)
    {t : Nat} (hb : b.Active t) (hts : c.shadowStart <= (t : Int)) (htc : t < c.birth) :
    ¬ D.Beats b t := by
  obtain ⟨r, hr, hrk⟩ := hshadow t hts htc
  intro hbeats
  have hle : rle r (b.routeAt t) := hbeats r hr
  rw [route_rle_iff_kappa, hrk, bridge_kappa_const b t hb] at hle
  exact hbetter.2 (klexLE_antisymm hbetter.1 hle)

/-- **step 6.**  A strictly-better bridge `c`, before it is even born, already
blocks `b` (through the deletion baseline carrying `κ_c`). -/
theorem better_future_bridge_blocks_before_birth {D : KDeleteFamily} {b c : Bridge}
    (hshadow : HasPrebirthShadow D c) (hbetter : klexLT c.kappa b.kappa)
    {t : Nat} (hb : b.Active t) (hts : c.shadowStart ≤ (t : Int)) (htc : t < c.birth) :
    rle (b.routeAt t) (D.best t) := by
  obtain ⟨r, hr, hrk⟩ := hshadow t hts htc
  have h1 : rle (b.routeAt t) r := by
    rw [route_rle_iff_kappa, hrk, bridge_kappa_const b t hb]
    exact hbetter.1
  have h2 : rle r (D.best t) := by
    unfold KDeleteFamily.best
    exact rle_rmaxList r _ hr
  exact rle_trans _ _ _ h1 h2

end KDeleteAbstract

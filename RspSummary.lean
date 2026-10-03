import Std
import Repair

/-!
## Phase H (new) — step 5: generic ramp–spike–plateau summary (§9)

A cut-independent `RspShape` on an offset window `[lo, n]`: ramp `z` for `z < m`,
one spike at `z = m` with value `m+γ`, plateau `m` after.  Phase E's `RspRow` and
the §9.5 repair-edge families are both instances, so `P_run_eq` / `A_run_eq` and
the edge records share one summary theorem.
-/

namespace RspSummary

open Lcs RunRect Repair

/-- A generic 1-D ramp–spike–plateau shape on offsets `z ∈ [lo, n]`. -/
structure RspShape (f : Nat → Nat) (m γ : Nat) (lo n : Nat) : Prop where
  ramp : ∀ z, lo ≤ z → z < m → z ≤ n → f z = z
  spike : ∀ z, lo ≤ z → z = m → z ≤ n → f z = m + γ
  plateau : ∀ z, lo ≤ z → m < z → z ≤ n → f z = m

/-- The value formula of an RSP shape. -/
theorem RspShape.value {f : Nat → Nat} {m γ lo n : Nat} (h : RspShape f m γ lo n)
    {z : Nat} (hl : lo ≤ z) (hzn : z ≤ n) :
    f z = (if z < m then z else if z = m then m + γ else m) := by
  by_cases h1 : z < m
  · rw [if_pos h1, h.ramp z hl h1 hzn]
  · rw [if_neg h1]
    by_cases h2 : z = m
    · rw [if_pos h2, h.spike z hl h2 hzn]
    · rw [if_neg h2, h.plateau z hl (by omega) hzn]

/-- The ramp part is strictly increasing: `f z = z`. -/
theorem RspShape.ramp_mono {f : Nat → Nat} {m γ lo n : Nat} (h : RspShape f m γ lo n)
    {z₁ z₂ : Nat} (h1 : lo ≤ z₁) (h12 : z₁ ≤ z₂) (h2 : z₂ < m) (h3n : z₂ ≤ n) :
    f z₁ ≤ f z₂ := by
  rw [h.ramp z₁ h1 (by omega) (by omega), h.ramp z₂ (by omega) h2 h3n]
  omega

/-- **The three records cover the whole range**: every value is `≤ max n (m+γ)`,
so an RSP family's extremum is determined by its ramp-end / spike / plateau
records. -/
theorem RspShape.le {f : Nat → Nat} {m γ lo n : Nat} (h : RspShape f m γ lo n)
    {z : Nat} (hl : lo ≤ z) (hz : z ≤ n) : f z ≤ max n (m + γ) := by
  rw [h.value hl hz]
  by_cases h1 : z < m
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : z = m
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

/-- **§9 — the three records.**  For an RSP shape the threshold set `{z : λ ≤ f z}`
is exactly the ramp part `[λ, m-1]`, the spike `{m}` (if `λ ≤ m+γ`) and the
plateau `[m+1, n]` (if `λ ≤ m`) — i.e. it is determined by the three records
`(m-1, m-1)`, `(m, m+γ)`, `(n, m)`. -/
theorem RspShape.threshold {f : Nat → Nat} {m γ lo n : Nat} (h : RspShape f m γ lo n)
    {lam z : Nat} (hl : lo ≤ z) (hz : z ≤ n) :
    (lam ≤ f z ↔ (lam ≤ z ∧ z < m) ∨ (z = m ∧ lam ≤ m + γ) ∨ (m < z ∧ lam ≤ m)) := by
  rw [h.value hl hz]
  by_cases h1 : z < m
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : z = m
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

/-- **§9.5 left edge.**  The left-edge context `u ↦ L(a,u)` (K-offset `z = u-c`)
is an `RspShape` on `z ∈ [1, d-c]`. -/
theorem left_edge_context_rsp {q k : Nat → α} {Tq Tk ap bp c d : Nat} {αs' βs : α}
    [DecidableEq α]
    (hQp : ConstRun q Tq ap bp αs') (hK : ConstRun k Tk c d βs) (heq : αs' = βs)
    (hab : ap ≤ bp) (hap : 0 < ap) (hc : 0 < c) (hcd : c ≤ d) :
    RspShape (fun z => lcsLen q k bp (c + z - 1))
      (bp - ap + 1) (lcsLen q k (ap - 1) (c - 1)) 1 (d - c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz1 hz hzn
    have h := repair_edge_left_rsp hQp hK heq hab hap hc (u := c + z) (by omega) (by omega)
    have huc : (c + z) - c = z := by omega
    rw [huc, if_pos hz] at h
    simpa using h
  · intro z hz1 hz hzn
    have h := repair_edge_left_rsp hQp hK heq hab hap hc (u := c + z) (by omega) (by omega)
    have huc : (c + z) - c = z := by omega
    rw [huc, if_neg (by omega : ¬ z < bp - ap + 1), if_pos hz] at h
    simpa using h
  · intro z hz1 hz hzn
    have h := repair_edge_left_rsp hQp hK heq hab hap hc (u := c + z) (by omega) (by omega)
    have huc : (c + z) - c = z := by omega
    rw [huc, if_neg (by omega : ¬ z < bp - ap + 1),
        if_neg (by omega : ¬ z = bp - ap + 1)] at h
    simpa using h

end RspSummary

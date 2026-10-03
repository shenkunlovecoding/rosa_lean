import Std
import CreditRepairReduce

/-!
## Exact ROSA credit — §2 of `ROSA_Credit_New_Results`

*"对全体 owner 求和：候选总量是 `O(T(R_Q+R_K))`"* — summing the per-owner candidate
bounds over all owners gives

`C ≤ T(5·R_Q + 4·R_K) ≤ 5·T(R_Q + R_K)`,

so the repair-candidate set is `O(T(R_Q+R_K))` even though some boundary owners
enumerate a whole run.

The table of the note:

| owner kind | #owners ≤ | kept per owner ≤ | total |
|---|---:|---:|---:|
| Q-run strict interior | `T` | `2` per K-run | `2·T·R_K` |
| Q-run boundary | `2·R_Q` | whole K grid | `2·T·R_Q` |
| K-run strict interior | `T` | `3` per Q-run | `3·T·R_Q` |
| K-run boundary | `2·R_K` | whole Q grid | `2·T·R_K` |

This file formalizes the counting skeleton: the generic "sum of per-owner bounds
≤ #owners × bound" lemma, the run-list cover bounds (`Σ run lengths ≤ T`,
`Σ run interiors ≤ T`), the "≤ 2 candidates per strict-interior Q-owner"
corollary of §1, and the final arithmetic `C ≤ T(5·R_Q + 4·R_K)`.
-/

namespace CreditCandidateCount

open CreditRepair RosBridge

/-! ### Generic counting -/

/-- A sum of per-owner bounds is at most `#owners × bound`. -/
theorem sum_map_le_card_mul {α : Type} (l : List α) (f : α → Nat) (B : Nat)
    (h : ∀ x ∈ l, f x ≤ B) : (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have hx : f x ≤ B := h x (by simp)
    have hxs : (xs.map f).sum ≤ xs.length * B := ih (fun y hy => h y (by simp [hy]))
    have hmul : (xs.length + 1) * B = xs.length * B + B := Nat.succ_mul _ _
    omega

/-- Pointwise domination of a sum. -/
theorem sum_map_le_of_pointwise {α : Type} {l : List α} {f g : α → Nat}
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have hxs := ih (fun y hy => h y (by simp [hy]))
    have hx : f x ≤ g x := h x (by simp)
    omega

/-! ### Run lists -/

/-- Runs `(lo,hi)` in increasing, non-overlapping order. -/
def OrderedRuns (rs : List (Nat × Nat)) : Prop :=
  rs.Pairwise (fun r s => r.2 < s.1)

/-- **§2, run cover.**  Ordered runs inside `[0,T)` occupy at most `T` positions. -/
theorem sum_len_le_of_ordered (rs : List (Nat × Nat)) (T : Nat)
    (hord : OrderedRuns rs) (hlo : ∀ r ∈ rs, r.1 ≤ r.2) (hhi : ∀ r ∈ rs, r.2 < T) :
    (rs.map (fun r => r.2 - r.1 + 1)).sum ≤ T := by
  suffices h : ∀ s, (∀ r ∈ rs, s ≤ r.1) → (rs.map (fun r => r.2 - r.1 + 1)).sum ≤ T - s by
    exact h 0 (fun r _ => Nat.zero_le _)
  intro s
  induction rs generalizing s with
  | nil => intro _; simp
  | cons r rs ih =>
    intro hs
    unfold OrderedRuns at hord
    rw [List.pairwise_cons] at hord
    obtain ⟨hhead, htail⟩ := hord
    rw [List.map_cons, List.sum_cons]
    have hrec := ih htail (fun a ha => hlo a (by simp [ha])) (fun a ha => hhi a (by simp [ha]))
      (r.2 + 1) (fun a ha => by have := hhead a ha; omega)
    have hlo' : r.1 ≤ r.2 := hlo r (by simp)
    have hhi' : r.2 < T := hhi r (by simp)
    have hsr : s ≤ r.1 := hs r (by simp)
    omega

/-- **§2, interior owners.**  The strict-interior positions of the runs number at
most `T` as well (`Σ (len - 2) ≤ Σ (len) ≤ T`). -/
theorem sum_interior_le_of_ordered (rs : List (Nat × Nat)) (T : Nat)
    (hord : OrderedRuns rs) (hlo : ∀ r ∈ rs, r.1 ≤ r.2) (hhi : ∀ r ∈ rs, r.2 < T) :
    (rs.map (fun r => r.2 - r.1 - 1)).sum ≤ T :=
  Nat.le_trans (sum_map_le_of_pointwise (l := rs)
    (f := fun r => r.2 - r.1 - 1) (g := fun r => r.2 - r.1 + 1) (fun r _ => by omega))
    (sum_len_le_of_ordered rs T hord hlo hhi)

/-- Boundary owners occur at most `2 · #runs` times (left/right end of each run);
after deduplication the number of boundary owners is no larger. -/
theorem boundary_spots_length (rs : List (Nat × Nat)) :
    (rs.map (fun r => r.1) ++ rs.map (fun r => r.2)).length = 2 * rs.length := by
  rw [List.length_append, List.length_map, List.length_map]
  omega

/-! ### §1 ⟹ at most two candidates per strict-interior Q-owner -/

/-- The retained candidates of a strict-interior Q-owner: the §1 reduction keeps
at most two bridges and reproduces the whole envelope. -/
theorem strictInterior_keep_le_two (cs : List Bridge) (p : Nat) (k₁ k₂ : Bridge)
    (hbirth : ∀ b ∈ cs, b.p = p)
    (hk₁ : k₁ ∈ cs) (hk₂ : k₂ ∈ cs)
    (hk₁max : ∀ b ∈ cs, Route.rle (b.routeAt p) (k₁.routeAt p))
    (hsurv : ∀ b ∈ cs, p < b.death → b = k₂) :
    ∃ kept : List Bridge, kept.length ≤ 2 ∧
      ∀ t, p ≤ t →
        Route.rmaxList (activeRoutes cs t) = Route.rmaxList (activeRoutes kept t) :=
  ⟨[k₁, k₂], by simp,
    fun t ht => two_candidates_reproduce_envelope cs p k₁ k₂ hbirth hk₁ hk₂ hk₁max hsurv t ht⟩

/-! ### The final arithmetic -/

/-- **§2, candidate count.**  The four owner classes contribute at most
`2·T·R_K`, `2·T·R_Q`, `3·T·R_Q`, `2·T·R_K` candidates, and

`2·T·R_K + 2·T·R_Q + 3·T·R_Q + 2·T·R_K = T(5·R_Q + 4·R_K)`.

(`R_Q`, `R_K` are the maximum constant-run counts of `Q`, `K`; `T` bounds both
the owners and the per-owner enumeration.) -/
theorem repair_candidate_bound (T RQ RK nQI nQB nKI nKB : Nat)
    (hQI : nQI ≤ 2 * (T * RK)) (hQB : nQB ≤ 2 * (T * RQ))
    (hKI : nKI ≤ 3 * (T * RQ)) (hKB : nKB ≤ 2 * (T * RK)) :
    nQI + nQB + nKI + nKB ≤ T * (5 * RQ + 4 * RK) := by
  have h1 : nQI + nKB ≤ 4 * (T * RK) := by
    have := Nat.add_le_add hQI hKB
    omega
  have h2 : nQB + nKI ≤ 5 * (T * RQ) := by
    have := Nat.add_le_add hQB hKI
    omega
  have hexp : T * (5 * RQ + 4 * RK) = 5 * (T * RQ) + 4 * (T * RK) := by
    rw [Nat.mul_add]
    congr 1
    · rw [Nat.mul_left_comm]
    · rw [Nat.mul_left_comm]
  omega

/-- Weaker, symmetric form of the same bound: `C ≤ 5·T·(R_Q + R_K)`. -/
theorem repair_candidate_bound' (T RQ RK nQI nQB nKI nKB : Nat)
    (hQI : nQI ≤ 2 * (T * RK)) (hQB : nQB ≤ 2 * (T * RQ))
    (hKI : nKI ≤ 3 * (T * RQ)) (hKB : nKB ≤ 2 * (T * RK)) :
    nQI + nQB + nKI + nKB ≤ 5 * (T * (RQ + RK)) := by
  have h := repair_candidate_bound T RQ RK nQI nQB nKI nKB hQI hQB hKI hKB
  have hsum : 5 * RQ + 4 * RK ≤ 5 * (RQ + RK) := by omega
  have h1 : T * (5 * RQ + 4 * RK) ≤ T * (5 * (RQ + RK)) := Nat.mul_le_mul_left T hsum
  have h2 : T * (5 * (RQ + RK)) = 5 * (T * (RQ + RK)) := Nat.mul_left_comm T 5 (RQ + RK)
  rw [h2] at h1
  exact Nat.le_trans h h1

end CreditCandidateCount

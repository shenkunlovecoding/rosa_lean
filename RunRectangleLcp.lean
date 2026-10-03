import Std
import Lcs
import RunRectangle
import Repair

/-!
## Phase G / item 11 — forward (LCP) Run-Rectangle

The right-context analogue of §6.3.  For the same-symbol runs `Q=[a,b]`, `K=[c,d]`
and `p∈[a,b]`, `u∈[c,d]`, the forward context `R = lcpLen q k Tq Tk p u` is the
ramp–spike–plateau field in `X = b-p`, `Y = d-u`.
-/

open Lcs RunRect Repair

namespace RunRectLcp

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α]

theorem lcpLen_le_bound (q k : Nat → α) (Tq Tk p u : Nat) :
    lcpLen q k Tq Tk p u ≤ min (Tq - p - 1) (Tk - u - 1) := by
  apply maxPrefix_le
  intro R hR _
  omega

theorem lcpLen_eq_of {q k : Nat → α} {Tq Tk p u c : Nat}
    (hc : PrefixEq q k Tq Tk p u c) (hnot : ¬ PrefixEq q k Tq Tk p u (c + 1)) :
    lcpLen q k Tq Tk p u = c :=
  Nat.le_antisymm
    (Nat.le_of_not_lt (fun hlt =>
      hnot (prefixEq_mono (lcpLen_spec q k Tq Tk p u) (by omega))))
    (lcpLen_greatest hc)

/-- Different run symbols, matching strictly inside both runs. -/
theorem lcp_rectangle_symbol_ne {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p < b) (hu : c ≤ u) (hud : u < d) :
    lcpLen q k Tq Tk p u = 0 := by
  apply lcpLen_eq_of (prefixEq_zero q k Tq Tk p u)
  intro hcon
  have h0 : q (p + 1 + 0) = k (u + 1 + 0) := hcon.2.2 0 (List.mem_range.mpr (by omega))
  simp only [Nat.add_zero] at h0
  have hqp : q (p + 1) = αs := hQ.mem (p + 1) (by omega) (by omega)
  have hku : k (u + 1) = βs := hK.mem (u + 1) (by omega) (by omega)
  exact hne (by rw [← hqp, h0, hku])

/-- `X < Y`: the forward context stops at the Q run's right edge. -/
theorem lcp_rectangle_offset_lt {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d)
    (hxy : b - p < d - u) :
    lcpLen q k Tq Tk p u = b - p := by
  have hbT : b < Tq := hQ.hi_lt
  have hdT : d < Tk := hK.hi_lt
  apply lcpLen_eq_of
  · refine ⟨by omega, by omega, ?_⟩
    intro h hh
    rw [List.mem_range] at hh
    have hqp : q (p + 1 + h) = αs := hQ.mem _ (by omega) (by omega)
    have hku : k (u + 1 + h) = βs := hK.mem _ (by omega) (by omega)
    rw [hqp, hku, heq]
  · intro hcon
    have hb1 : b + 1 < Tq := by have := hcon.1; omega
    have hm : b - p ∈ List.range (b - p + 1) := List.mem_range.mpr (by omega)
    have h0 := hcon.2.2 (b - p) hm
    have hqx : q (p + 1 + (b - p)) ≠ αs := by
      have : p + 1 + (b - p) = b + 1 := by omega
      rw [this]; exact hQ.right_ne hb1
    have hkx : k (u + 1 + (b - p)) = βs := hK.mem _ (by omega) (by omega)
    exact hqx (by rw [h0, hkx, ← heq])

/-- `Y < X`: the forward context stops at the K run's right edge. -/
theorem lcp_rectangle_offset_gt {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d)
    (hxy : d - u < b - p) :
    lcpLen q k Tq Tk p u = d - u := by
  have hbT : b < Tq := hQ.hi_lt
  have hdT : d < Tk := hK.hi_lt
  apply lcpLen_eq_of
  · refine ⟨by omega, by omega, ?_⟩
    intro h hh
    rw [List.mem_range] at hh
    have hqp : q (p + 1 + h) = αs := hQ.mem _ (by omega) (by omega)
    have hku : k (u + 1 + h) = βs := hK.mem _ (by omega) (by omega)
    rw [hqp, hku, heq]
  · intro hcon
    have hd1 : d + 1 < Tk := by have := hcon.2.1; omega
    have hm : d - u ∈ List.range (d - u + 1) := List.mem_range.mpr (by omega)
    have h0 := hcon.2.2 (d - u) hm
    have hkx : k (u + 1 + (d - u)) ≠ βs := by
      have : u + 1 + (d - u) = d + 1 := by omega
      rw [this]; exact hK.right_ne hd1
    have hqx : q (p + 1 + (d - u)) = αs := hQ.mem _ (by omega) (by omega)
    exact hkx (by rw [← h0, hqx, heq])

/-- `X = Y`: both runs end together and the context recurses into the next run pair. -/
theorem lcp_rectangle_offset_eq {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d)
    (hxy : b - p = d - u) :
    lcpLen q k Tq Tk p u = (b - p) + lcpLen q k Tq Tk b d := by
  have hbT : b < Tq := hQ.hi_lt
  have hdT : d < Tk := hK.hi_lt
  have hnotb : ¬ PrefixEq q k Tq Tk b d (lcpLen q k Tq Tk b d + 1) := by
    intro hc'
    have := lcpLen_greatest hc'
    omega
  apply lcpLen_eq_of
  · have hLb := lcpLen_le_bound q k Tq Tk b d
    have hLq : lcpLen q k Tq Tk b d ≤ Tq - b - 1 := Nat.le_trans hLb (Nat.min_le_left _ _)
    have hLk : lcpLen q k Tq Tk b d ≤ Tk - d - 1 := Nat.le_trans hLb (Nat.min_le_right _ _)
    refine ⟨by omega, by omega, ?_⟩
    intro h hh
    rw [List.mem_range] at hh
    by_cases hcase : h < b - p
    · have hqp : q (p + 1 + h) = αs := hQ.mem _ (by omega) (by omega)
      have hku : k (u + 1 + h) = βs := hK.mem _ (by omega) (by omega)
      rw [hqp, hku, heq]
    · have hge : b - p ≤ h := by omega
      have hsub : h - (b - p) < lcpLen q k Tq Tk b d := by omega
      have hidxq : p + 1 + h = b + 1 + (h - (b - p)) := by omega
      have hidxk : u + 1 + h = d + 1 + (h - (b - p)) := by omega
      have hs := (lcpLen_spec q k Tq Tk b d).2.2 (h - (b - p))
        (List.mem_range.mpr hsub)
      rw [hidxq, hidxk]; exact hs
  · intro hcon
    apply hnotb
    have hb1 := hcon.1
    have hb2 := hcon.2.1
    refine ⟨by omega, by omega, ?_⟩
    intro h' hh'
    rw [List.mem_range] at hh'
    have hxh : b - p + h' ∈ List.range (b - p + lcpLen q k Tq Tk b d + 1) :=
      List.mem_range.mpr (by omega)
    have h0 := hcon.2.2 (b - p + h') hxh
    have hidxq : p + 1 + (b - p + h') = b + 1 + h' := by omega
    have hidxk : u + 1 + (b - p + h') = d + 1 + h' := by omega
    rw [hidxq, hidxk] at h0
    exact h0

/-- RSP row shape for the right context (item 11). -/
theorem repair_edge_right_rsp {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d) :
    lcpLen q k Tq Tk p u =
      (if b - p < d - u then b - p
       else if b - p = d - u then (b - p) + lcpLen q k Tq Tk b d
       else d - u) := by
  by_cases h1 : b - p < d - u
  · rw [if_pos h1]
    exact lcp_rectangle_offset_lt hQ hK heq hp hpb hu hud h1
  · rw [if_neg h1]
    by_cases h2 : b - p = d - u
    · rw [if_pos h2]
      exact lcp_rectangle_offset_eq hQ hK heq hp hpb hu hud h2
    · rw [if_neg h2]
      exact lcp_rectangle_offset_gt hQ hK heq hp hpb hu hud (by omega)

end RunRectLcp

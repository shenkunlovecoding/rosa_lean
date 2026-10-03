import Std
import Lcs

/-!
## Phase C — Run-Rectangle LCS Theorem (§6.3)

For a maximal constant run `Q_i = [a,b]` of `q` (symbol `αs`) and `K_j = [c,d]` of
`k` (symbol `βs`), with `t ∈ [a,b]`, `e ∈ [c,d]` and offsets `x = t-a+1`,
`y = e-c+1`:

* `αs ≠ βs`            → `lcsLen = 0`
* `αs = βs`, `x < y`   → `lcsLen = x`
* `αs = βs`, `y < x`   → `lcsLen = y`
* `αs = βs`, `x = y`   → `lcsLen = x + lcsLen q k (a-1) (c-1)`  (needs `a,c > 0`)
-/

open Lcs

namespace RunRect

variable {α : Type} [DecidableEq α]

/-- `[lo,hi]` is a maximal constant run of `s` (length `T`) with symbol `sym`. -/
structure ConstRun (s : Nat → α) (T lo hi : Nat) (sym : α) : Prop where
  hi_lt : hi < T
  mem : ∀ x, lo ≤ x → x ≤ hi → s x = sym
  left_ne : 0 < lo → s (lo - 1) ≠ sym
  right_ne : hi + 1 < T → s (hi + 1) ≠ sym

/-- The three-way split of the rectangle: different symbols give length 0. -/
theorem run_rectangle_symbol_ne {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b) (he : c ≤ e) (hed : e ≤ d) :
    lcsLen q k t e = 0 := by
  apply lcsLen_eq_of (suffixEq_zero q k t e)
  intro hcon
  have h0 : q (t - 0) = k (e - 0) := hcon.2.2 0 (List.mem_range.mpr (by omega))
  simp only [Nat.sub_zero] at h0
  have hqt : q t = αs := hQ.mem t ht htb
  have hke : k e = βs := hK.mem e he hed
  exact hne (by rw [← hqt, h0, hke])

/-- Same symbol, `x < y` (Q offset smaller): the suffix stops at the Q run's left edge. -/
theorem run_rectangle_offset_lt {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b) (he : c ≤ e) (hed : e ≤ d)
    (hxy : t - a < e - c) :
    lcsLen q k t e = t - a + 1 := by
  apply lcsLen_eq_of
  · refine ⟨by omega, by omega, ?_⟩
    intro h hh
    rw [List.mem_range] at hh
    have hqt : q (t - h) = αs := hQ.mem (t - h) (by omega) (by omega)
    have hke : k (e - h) = βs := hK.mem (e - h) (by omega) (by omega)
    rw [hqt, hke, heq]
  · intro hcon
    rcases Nat.eq_zero_or_pos a with ha | ha
    · have := hcon.1; omega
    · have hxm : t - a + 1 ∈ List.range (t - a + 1 + 1) := List.mem_range.mpr (by omega)
      have h0 := hcon.2.2 (t - a + 1) hxm
      have hqx : q (t - (t - a + 1)) ≠ αs := by
        have : t - (t - a + 1) = a - 1 := by omega
        rw [this]; exact hQ.left_ne ha
      have hkx : k (e - (t - a + 1)) = βs := hK.mem _ (by omega) (by omega)
      exact hqx (by rw [h0, hkx, ← heq])

/-- Same symbol, `y < x` (K offset smaller): symmetric. -/
theorem run_rectangle_offset_gt {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b) (he : c ≤ e) (hed : e ≤ d)
    (hxy : e - c < t - a) :
    lcsLen q k t e = e - c + 1 := by
  apply lcsLen_eq_of
  · refine ⟨by omega, by omega, ?_⟩
    intro h hh
    rw [List.mem_range] at hh
    have hqt : q (t - h) = αs := hQ.mem (t - h) (by omega) (by omega)
    have hke : k (e - h) = βs := hK.mem (e - h) (by omega) (by omega)
    rw [hqt, hke, heq]
  · intro hcon
    rcases Nat.eq_zero_or_pos c with hc | hc
    · have := hcon.2.1; omega
    · have hem : e - c + 1 ∈ List.range (e - c + 1 + 1) := List.mem_range.mpr (by omega)
      have h0 := hcon.2.2 (e - c + 1) hem
      have hkx : k (e - (e - c + 1)) ≠ βs := by
        have : e - (e - c + 1) = c - 1 := by omega
        rw [this]; exact hK.left_ne hc
      have hqx : q (t - (e - c + 1)) = αs := hQ.mem _ (by omega) (by omega)
      exact hkx (by rw [← h0, hqx, heq])

/-- Same symbol, `x = y`: the rectangle "spikes" into the diagonal predecessor. -/
theorem run_rectangle_offset_eq {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b) (he : c ≤ e) (hed : e ≤ d)
    (hxy : t - a = e - c) :
    lcsLen q k t e = (t - a + 1) + lcsLen q k (a - 1) (c - 1) := by
  have htx : t - (t - a + 1) = a - 1 := by omega
  have hex : e - (t - a + 1) = c - 1 := by omega
  have hgm_le : lcsLen q k (a - 1) (c - 1) ≤ a := by
    have := lcsLen_le_bound q k (a - 1) (c - 1); omega
  have hgm_le' : lcsLen q k (a - 1) (c - 1) ≤ c := by
    have := lcsLen_le_bound q k (a - 1) (c - 1); omega
  have hnotgm : ¬ SuffixEq q k (a - 1) (c - 1) (lcsLen q k (a - 1) (c - 1) + 1) := by
    intro hc'
    have := lcsLen_greatest hc'
    omega
  apply lcsLen_eq_of
  · refine ⟨by omega, by omega, ?_⟩
    intro h hh
    rw [List.mem_range] at hh
    by_cases hcase : h < t - a + 1
    · have hqt : q (t - h) = αs := hQ.mem (t - h) (by omega) (by omega)
      have hke : k (e - h) = βs := hK.mem (e - h) (by omega) (by omega)
      rw [hqt, hke, heq]
    · have hge : t - a + 1 ≤ h := by omega
      have hsub : h - (t - a + 1) < lcsLen q k (a - 1) (c - 1) := by omega
      have htth : t - h = (a - 1) - (h - (t - a + 1)) := by omega
      have heth : e - h = (c - 1) - (h - (t - a + 1)) := by omega
      have hs := (lcsLen_spec q k (a - 1) (c - 1)).2.2 (h - (t - a + 1))
        (List.mem_range.mpr hsub)
      rw [htth, heth]; exact hs
  · intro hcon
    have hb1 := hcon.1
    have hb2 := hcon.2.1
    apply hnotgm
    refine ⟨by omega, by omega, ?_⟩
    intro h' hh'
    rw [List.mem_range] at hh'
    have hxh : (t - a + 1) + h' ∈
        List.range ((t - a + 1) + lcsLen q k (a - 1) (c - 1) + 1) :=
      List.mem_range.mpr (by omega)
    have h0 := hcon.2.2 ((t - a + 1) + h') hxh
    have htth : t - ((t - a + 1) + h') = (a - 1) - h' := by omega
    have heth : e - ((t - a + 1) + h') = (c - 1) - h' := by omega
    rw [htth, heth] at h0
    exact h0

/-- RSP row shape (§7): inside a fixed `α=β` rectangle, `lcsLen` at `e` is
ramp (`y < x`), a single spike (`y = x`) or plateau (`y > x`). -/
theorem run_rectangle_rsp {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b) (he : c ≤ e) (hed : e ≤ d) :
    lcsLen q k t e =
      (if e - c + 1 < t - a + 1 then e - c + 1
       else if e - c + 1 = t - a + 1 then (t - a + 1) + lcsLen q k (a - 1) (c - 1)
       else t - a + 1) := by
  by_cases h1 : e - c + 1 < t - a + 1
  · rw [if_pos h1]
    exact run_rectangle_offset_gt hQ hK heq ht htb he hed (by omega)
  · rw [if_neg h1]
    by_cases h2 : e - c + 1 = t - a + 1
    · rw [if_pos h2]
      exact run_rectangle_offset_eq hQ hK heq ha hc ht htb he hed (by omega)
    · rw [if_neg h2]
      exact run_rectangle_offset_lt hQ hK heq ht htb he hed (by omega)

/-- §6.4 run-grid recurrence (RG).  `γ_{ij}` is the LCSuffix at the end of the
previous run pair `(Q_{i-1},K_{j-1}) = ([ap,bp],[cp,dp])`; it obeys the same
three-way formula: `0` when symbols differ, otherwise `min(m,n)` / `m+γ` with
`m = bp-ap+1`, `n = dp-cp+1`. -/
theorem run_grid_gamma_recurrence {q k : Nat → α} {Tq Tk ap bp cp dp : Nat} {αp βp : α}
    (hQp : ConstRun q Tq ap bp αp) (hKp : ConstRun k Tk cp dp βp)
    (hapb : ap ≤ bp) (hcpd : cp ≤ dp) (hap : 0 < ap) (hcp : 0 < cp) :
    (αp ≠ βp → lcsLen q k bp dp = 0) ∧
    (αp = βp →
      lcsLen q k bp dp =
        (if dp - cp + 1 < bp - ap + 1 then dp - cp + 1
         else if dp - cp + 1 = bp - ap + 1 then (bp - ap + 1) + lcsLen q k (ap - 1) (cp - 1)
         else bp - ap + 1)) := by
  refine ⟨?_, ?_⟩
  · intro hne
    exact run_rectangle_symbol_ne hQp hKp hne hapb (Nat.le_refl bp) hcpd (Nat.le_refl dp)
  · intro heq
    exact run_rectangle_rsp hQp hKp heq hap hcp hapb (Nat.le_refl bp) hcpd (Nat.le_refl dp)

end RunRect

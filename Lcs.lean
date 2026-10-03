import Std

set_option linter.unusedSectionVars false

/-!
## Phase B — LCSuffix on functional strings
-/

namespace Lcs

variable {α : Type} [DecidableEq α]

/-- The length-`L` suffix of `q[..t]` equals the length-`L` suffix of `k[..e]`. -/
def SuffixEq (q k : Nat → α) (t e L : Nat) : Prop :=
  L ≤ t + 1 ∧ L ≤ e + 1 ∧ ∀ h ∈ List.range L, q (t - h) = k (e - h)

theorem suffixEq_iff_all (q k : Nat → α) (t e L : Nat) :
    SuffixEq q k t e L ↔
      L ≤ t + 1 ∧ L ≤ e + 1 ∧
        (List.range L).all (fun h => decide (q (t - h) = k (e - h))) = true := by
  unfold SuffixEq
  constructor
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, ?_⟩
    rw [List.all_eq_true]
    intro x hx
    rw [decide_eq_true_eq]
    exact c x hx
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, ?_⟩
    intro x hx
    have h := (List.all_eq_true.mp c) x hx
    rwa [decide_eq_true_eq] at h

instance (q k : Nat → α) (t e L : Nat) : Decidable (SuffixEq q k t e L) :=
  decidable_of_iff'
    (L ≤ t + 1 ∧ L ≤ e + 1 ∧
      (List.range L).all (fun h => decide (q (t - h) = k (e - h))) = true)
    (suffixEq_iff_all q k t e L)

theorem suffixEq_zero (q k : Nat → α) (t e : Nat) : SuffixEq q k t e 0 := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
  intro h hh; simp at hh

theorem suffixEq_mono {q k : Nat → α} {t e L L' : Nat}
    (h : SuffixEq q k t e L) (hL : L' ≤ L) : SuffixEq q k t e L' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  intro h' hh
  rw [List.mem_range] at hh
  exact h3 h' (List.mem_range.mpr (by omega))

theorem suffixEq_max {q k : Nat → α} {t e a b : Nat}
    (ha : SuffixEq q k t e a) (hb : SuffixEq q k t e b) : SuffixEq q k t e (max a b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨by omega, by omega, ?_⟩
  intro h hh
  rw [List.mem_range] at hh
  rcases Nat.le_total a b with hab | hba
  · exact hb3 h (List.mem_range.mpr (by omega))
  · exact ha3 h (List.mem_range.mpr (by omega))

/-- Max over the satisfying lengths `< n` (with `0` as the default). -/
def maxSuffix (q k : Nat → α) (t e : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if SuffixEq q k t e n then max n (maxSuffix q k t e n) else maxSuffix q k t e n

theorem maxSuffix_spec (q k : Nat → α) (t e : Nat) :
    ∀ n, SuffixEq q k t e (maxSuffix q k t e n) := by
  intro n
  induction n with
  | zero => rw [maxSuffix]; exact suffixEq_zero q k t e
  | succ m ih =>
    rw [maxSuffix]
    by_cases h : SuffixEq q k t e m
    · rw [if_pos h]; exact suffixEq_max h ih
    · rw [if_neg h]; exact ih

theorem maxSuffix_le (q k : Nat → α) (t e : Nat) :
    ∀ n m, (∀ L, L < n → SuffixEq q k t e L → L ≤ m) → maxSuffix q k t e n ≤ m := by
  intro n
  induction n with
  | zero => intro m _; rw [maxSuffix]; exact Nat.zero_le m
  | succ n ih =>
    intro m h
    rw [maxSuffix]
    by_cases hc : SuffixEq q k t e n
    · rw [if_pos hc]
      have h1 : n ≤ m := h n (by omega) hc
      have h2 : maxSuffix q k t e n ≤ m := ih m (fun L hL hs => h L (by omega) hs)
      omega
    · rw [if_neg hc]
      exact ih m (fun L hL hs => h L (by omega) hs)

theorem maxSuffix_greatest (q k : Nat → α) (t e : Nat) :
    ∀ n L, SuffixEq q k t e L → L < n → L ≤ maxSuffix q k t e n := by
  intro n
  induction n with
  | zero => intro L _ hL; omega
  | succ n ih =>
    intro L hs hL
    rw [maxSuffix]
    by_cases hc : SuffixEq q k t e n
    · rw [if_pos hc]
      have hcase : L = n ∨ L < n := by omega
      rcases hcase with heq | hlt
      · subst heq; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih L hs hlt) (Nat.le_max_right _ _)
    · rw [if_neg hc]
      have hlt : L < n := by
        have hcase : L = n ∨ L < n := by omega
        rcases hcase with heq | hlt
        · subst heq; exact absurd hs hc
        · exact hlt
      exact ih L hs hlt

/-- `lcsLen q k t e`: the LCSuffix of `q[..t]` and `k[..e]`. -/
def lcsLen (q k : Nat → α) (t e : Nat) : Nat :=
  maxSuffix q k t e (min (t + 1) (e + 1) + 1)

theorem lcsLen_spec (q k : Nat → α) (t e : Nat) : SuffixEq q k t e (lcsLen q k t e) :=
  maxSuffix_spec q k t e _

theorem lcsLen_greatest {q k : Nat → α} {t e L : Nat} (h : SuffixEq q k t e L) :
    L ≤ lcsLen q k t e := by
  apply maxSuffix_greatest
  · exact h
  · have h1 := h.1; have h2 := h.2.1; omega

theorem lcsLen_le_bound (q k : Nat → α) (t e : Nat) :
    lcsLen q k t e ≤ min (t + 1) (e + 1) := by
  apply maxSuffix_le
  intro L hL _
  omega

theorem lcsLen_le_of_not {q k : Nat → α} {t e L : Nat}
    (h : ¬ SuffixEq q k t e (L + 1)) : lcsLen q k t e ≤ L :=
  Nat.le_of_not_lt (fun hlt => h (suffixEq_mono (lcsLen_spec q k t e) (by omega)))

/-- Master characterisation. -/
theorem lcsLen_eq_of {q k : Nat → α} {t e c : Nat}
    (hc : SuffixEq q k t e c) (hnot : ¬ SuffixEq q k t e (c + 1)) :
    lcsLen q k t e = c :=
  Nat.le_antisymm (lcsLen_le_of_not hnot) (lcsLen_greatest hc)

end Lcs

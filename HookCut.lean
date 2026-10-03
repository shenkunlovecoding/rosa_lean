import Route
import CutArith

/-!
## §4.3 Hook-Envelope Theorem

`KCut(t,s) = max { A(s), P(s), R(s) }` where
* `A(s)` = best candidate with `e < s`,
* `P(s)` = best candidate with `δ_e > s` (nothing truncated),
* `R(s)` = ramp/plateau term from the maximal endpoint with `δ_e ≤ s`.
-/

open Route

namespace HookCut
open CutArith

def ApartC (ell : Nat → Int) (t s : Nat) : Route := rmaxList (apartList ell t s)
def PpartC (ell : Nat → Int) (t s : Nat) : Route := rmaxList (ppartList ell t s)
def RpartC (ell : Nat → Int) (t s : Nat) : Route := rpart ell t s

def hookCut (ell : Nat → Int) (t s : Nat) : Route :=
  rmax (ApartC ell t s) (rmax (PpartC ell t s) (RpartC ell t s))

/-! ### Validity -/

theorem valid_apartList (ell : Nat → Int) (t s : Nat) :
    ∀ r ∈ apartList ell t s, Valid r := by
  intro r hr
  unfold apartList at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, rfl⟩ := hr
  rw [List.mem_filter] at he
  obtain ⟨_, hp⟩ := he
  simp only [decide_eq_true_eq] at hp
  exact valid_pair (ell e) (e : Int) hp.2 (by omega)

theorem valid_ppartList (ell : Nat → Int) (t s : Nat) :
    ∀ r ∈ ppartList ell t s, Valid r := by
  intro r hr
  unfold ppartList at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, rfl⟩ := hr
  rw [List.mem_filter] at he
  obtain ⟨_, hp⟩ := he
  simp only [decide_eq_true_eq] at hp
  exact valid_pair (ell e) (e : Int) hp.1 (by omega)

theorem valid_RpartC (ell : Nat → Int) (t s : Nat) : Valid (RpartC ell t s) := by
  unfold RpartC rpart
  by_cases h : (s : Int) < umax ell t s
  · rw [if_pos h]; exact valid_mk _ _ (neg_one_le_foldr_max _)
  · rw [if_neg h]; exact valid_unmatched

theorem valid_hookCut (ell : Nat → Int) (t s : Nat) : Valid (hookCut ell t s) := by
  unfold hookCut
  exact valid_rmax _ _
    (valid_rmaxList _ (valid_apartList ell t s))
    (valid_rmax _ _ (valid_rmaxList _ (valid_ppartList ell t s)) (valid_RpartC ell t s))

theorem valid_kcutCand (ell : Nat → Int) (s e : Nat) : Valid (kcutCand ell s e) := by
  unfold kcutCand
  by_cases h1 : e < s
  · rw [if_pos h1]; exact valid_mk _ _ (by omega)
  · rw [if_neg h1]
    by_cases h2 : e = s
    · rw [if_pos h2]; exact valid_unmatched
    · rw [if_neg h2]; exact valid_mk _ _ (by omega)

theorem valid_bruteKCut (ell : Nat → Int) (t s : Nat) : Valid (bruteKCut ell t s) := by
  unfold bruteKCut
  apply valid_rmaxList
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨e, _, rfl⟩ := hr
  exact valid_kcutCand ell s e

/-! ### `foldr max (-1)` attainment -/

theorem umax_mem (ell : Nat → Int) (t s : Nat) (h : 0 < umax ell t s) :
    ∃ (e : Nat), (e : Int) = umax ell t s ∧ e < t ∧ 0 < ell e ∧ (e : Int) - ell e ≤ (s : Int) := by
  have hne : uList ell t s ≠ [] := by
    intro hc
    unfold umax at h
    rw [hc, List.foldr_nil] at h
    omega
  have hmem : (uList ell t s).foldr max (-1) ∈ uList ell t s :=
    foldr_max_mem (uList ell t s) hne (fun x hx => by
      unfold uList at hx
      rw [List.mem_map] at hx
      obtain ⟨e, _, hxe⟩ := hx
      rw [← hxe]; omega)
  unfold uList at hmem
  rw [List.mem_map] at hmem
  obtain ⟨e, he, heq⟩ := hmem
  rw [List.mem_filter] at he
  obtain ⟨hm, hp⟩ := he
  rw [List.mem_range] at hm
  simp only [decide_eq_true_eq] at hp
  exact ⟨e, by unfold umax; exact heq, hm, hp.1, hp.2⟩

/-! ### Direction 1: every brute candidate is below the hook cut -/

theorem kcutCand_le_hookCut (ell : Nat → Int) (t s e : Nat) (he : e < t) :
    rle (kcutCand ell s e) (hookCut ell t s) := by
  have hA : rle (ApartC ell t s) (hookCut ell t s) := by
    unfold hookCut; exact rle_rmax_left _ _
  have hP : rle (PpartC ell t s) (hookCut ell t s) := by
    unfold hookCut
    exact rle_trans _ _ _ (rle_rmax_left _ _) (rle_rmax_right _ _)
  have hR : rle (RpartC ell t s) (hookCut ell t s) := by
    unfold hookCut
    exact rle_trans _ _ _ (rle_rmax_right _ _) (rle_rmax_right _ _)
  unfold kcutCand
  by_cases h1 : e < s
  · rw [if_pos h1]
    by_cases hle : ell e ≤ 0
    · rw [mk_nonpos _ _ hle]; exact valid_rle_unmatched _ (valid_hookCut ell t s)
    · rw [mk_pos _ _ (by omega)]
      apply rle_trans _ _ _ _ hA
      apply rle_rmaxList
      rw [mem_apartList]
      exact ⟨he, h1, by omega⟩
  · rw [if_neg h1]
    by_cases h2 : e = s
    · rw [if_pos h2]; exact valid_rle_unmatched _ (valid_hookCut ell t s)
    · rw [if_neg h2]
      have hse : s < e := by omega
      rw [hook_split ell s e hse]
      by_cases hd : (e : Int) - ell e ≤ (s : Int)
      · rw [if_pos hd]
        by_cases hle : (e : Int) - (s : Int) ≤ 0
        · rw [mk_nonpos _ _ hle]; exact valid_rle_unmatched _ (valid_hookCut ell t s)
        · rw [mk_pos _ _ (by omega)]
          apply rle_trans _ _ _ _ hR
          have hmin : min (ell e) ((e : Int) - (s : Int)) = (e : Int) - (s : Int) := by
            rw [hook_split ell s e hse, if_pos hd]
          have hellpos : 0 < ell e := by
            have : (e : Int) - (s : Int) ≤ ell e := by
              rw [← hmin]; exact Int.min_le_left _ _
            omega
          have humax : (e : Int) ≤ umax ell t s := by
            have := le_foldr_max (uList ell t s) (e : Int)
              (by rw [mem_uList]; exact ⟨he, hellpos, hd⟩)
            simpa [umax] using this
          have hsmax : (s : Int) < umax ell t s := by omega
          unfold RpartC rpart
          rw [if_pos hsmax, mk_pos _ _ (by omega)]
          unfold rle; dsimp only; omega
      · rw [if_neg hd]
        by_cases hell : ell e ≤ 0
        · rw [mk_nonpos _ _ hell]; exact valid_rle_unmatched _ (valid_hookCut ell t s)
        · rw [mk_pos _ _ (by omega)]
          apply rle_trans _ _ _ _ hP
          apply rle_rmaxList
          rw [mem_ppartList]
          exact ⟨he, by omega, by omega⟩

theorem bruteKCut_le_hookCut (ell : Nat → Int) (t s : Nat) :
    rle (bruteKCut ell t s) (hookCut ell t s) := by
  unfold bruteKCut
  apply rmaxList_lub
  · exact valid_hookCut ell t s
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨e, he, rfl⟩ := hr
    rw [List.mem_range] at he
    exact kcutCand_le_hookCut ell t s e he

/-! ### Direction 2: each hook piece is realized by a brute candidate -/

theorem rle_apartList_brute (ell : Nat → Int) (t s : Nat) :
    rle (ApartC ell t s) (bruteKCut ell t s) := by
  unfold ApartC bruteKCut
  apply rmaxList_lub
  · exact valid_bruteKCut ell t s
  · intro r hr
    unfold apartList at hr
    rw [List.mem_map] at hr
    obtain ⟨e, he, rfl⟩ := hr
    rw [List.mem_filter] at he
    obtain ⟨hm, hp⟩ := he
    rw [List.mem_range] at hm
    simp only [decide_eq_true_eq] at hp
    apply rle_rmaxList
    rw [List.mem_map]
    exact ⟨e, by rw [List.mem_range]; exact hm, by
      unfold kcutCand; rw [if_pos hp.1]; exact mk_pos _ _ hp.2⟩

theorem rle_ppartList_brute (ell : Nat → Int) (t s : Nat) :
    rle (PpartC ell t s) (bruteKCut ell t s) := by
  unfold PpartC bruteKCut
  apply rmaxList_lub
  · exact valid_bruteKCut ell t s
  · intro r hr
    unfold ppartList at hr
    rw [List.mem_map] at hr
    obtain ⟨e, he, rfl⟩ := hr
    rw [List.mem_filter] at he
    obtain ⟨hm, hp⟩ := he
    rw [List.mem_range] at hm
    simp only [decide_eq_true_eq] at hp
    have hse : s < e := by
      have h1 : (s : Int) < (e : Int) := by omega
      omega
    apply rle_rmaxList
    rw [List.mem_map]
    refine ⟨e, by rw [List.mem_range]; exact hm, ?_⟩
    unfold kcutCand
    rw [if_neg (by omega : ¬ e < s), if_neg (by omega : ¬ e = s)]
    rw [hook_split ell s e hse, if_neg (by omega : ¬ ((e : Int) - ell e ≤ (s : Int)))]
    exact mk_pos _ _ hp.1

theorem rle_rpart_brute (ell : Nat → Int) (t s : Nat) :
    rle (RpartC ell t s) (bruteKCut ell t s) := by
  unfold RpartC rpart
  by_cases h : (s : Int) < umax ell t s
  · rw [if_pos h]
    have hpos : 0 < umax ell t s := by omega
    obtain ⟨e, heq, het, hell, hd⟩ := umax_mem ell t s hpos
    have hse : s < e := by omega
    rw [mk_pos _ _ (by omega : 0 < umax ell t s - (s : Int))]
    unfold bruteKCut
    apply rle_rmaxList
    rw [List.mem_map]
    refine ⟨e, by rw [List.mem_range]; exact het, ?_⟩
    unfold kcutCand
    rw [if_neg (by omega : ¬ e < s), if_neg (by omega : ¬ e = s)]
    rw [hook_split ell s e hse, if_pos (by omega : (e : Int) - ell e ≤ (s : Int))]
    rw [mk_pos _ _ (by omega : 0 < (e : Int) - (s : Int)), heq]
  · rw [if_neg h]; exact valid_rle_unmatched _ (valid_bruteKCut ell t s)

/-! ### Hook-Envelope Theorem -/

theorem kcut_hook_decomposition (ell : Nat → Int) (t s : Nat) :
    bruteKCut ell t s = hookCut ell t s := by
  apply rle_antisymm
  · exact bruteKCut_le_hookCut ell t s
  · unfold hookCut
    exact (rle_rmax_lub _ _ _).mpr
      ⟨rle_apartList_brute ell t s,
       (rle_rmax_lub _ _ _).mpr ⟨rle_ppartList_brute ell t s, rle_rpart_brute ell t s⟩⟩

end HookCut

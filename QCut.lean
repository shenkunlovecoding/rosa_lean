import Route
import CutArith

/-!
## §5 Bulk Q-Cut

For a Q owner `u ≤ t` the cut length is `min(L_base, t-u)` and the endpoint is
the latest `e < t` with `ell e ≥ λ`.  We prove this closed form equals the
pointwise brute max `max_e min(ell e, t-u)`.

**Future owner `t < u`:** the owner is not inside the query suffix, so the route
is unconstrained — it equals the base route.  This case is handled explicitly
(`qtCut_future`): previously the cap `t-u` went negative and every candidate
collapsed to `unmatched`, which was a specification bug.
-/

open Route

namespace QCut
open CutArith

/-- `L_base(t)`: the best length in row `t`. -/
def Lbase (ell : Nat → Int) (t : Nat) : Int :=
  ((List.range t).map (fun e => ell e)).foldr max (-1)

/-- Endpoints `e` whose length reaches the threshold `lam`. -/
def latestList (ell : Nat → Int) (t : Nat) (lam : Int) : List Int :=
  ((List.range t).filter (fun e => decide (lam ≤ ell e))).map (fun (e : Nat) => (e : Int))

/-- The latest endpoint reaching the threshold (`-1` if none). -/
def latest (ell : Nat → Int) (t : Nat) (lam : Int) : Int := (latestList ell t lam).foldr max (-1)

/-- Base route (no cut): the unconstrained max `(ℓ_e, e)` over `e < t`. -/
def baseRoute (ell : Nat → Int) (t : Nat) : Route :=
  CutArith.mk (Lbase ell t) (latest ell t (Lbase ell t))

/-- Per-endpoint Q-cut candidate.  A future owner (`t < u`) imposes no cap;
otherwise the length is capped at `t-u`. -/
def qcutCand (ell : Nat → Int) (t u e : Nat) : Route :=
  if t < u then CutArith.mk (ell e) (e : Int)
  else CutArith.mk (min (ell e) ((t : Int) - (u : Int))) (e : Int)

/-- Pointwise brute Q-cut; a future owner gives the base route. -/
def bruteQCut (ell : Nat → Int) (t u : Nat) : Route :=
  if t < u then baseRoute ell t
  else rmaxList ((List.range t).map fun e => qcutCand ell t u e)

/-- The closed-form cut length: `t-u` capped by `L_base` (base for `t < u`). -/
def qcutLambda (ell : Nat → Int) (t u : Nat) : Int :=
  if t < u then Lbase ell t else min (Lbase ell t) ((t : Int) - (u : Int))

/-- The closed-form Q-cut route. -/
def qcutClosed (ell : Nat → Int) (t u : Nat) : Route :=
  CutArith.mk (qcutLambda ell t u) (latest ell t (qcutLambda ell t u))

/-! ### List lemmas -/

theorem le_Lbase (ell : Nat → Int) (t e : Nat) (h : e < t) : ell e ≤ Lbase ell t := by
  unfold Lbase
  exact le_foldr_max _ _ (by rw [List.mem_map]; exact ⟨e, by rw [List.mem_range]; exact h, rfl⟩)

theorem Lbase_attained (ell : Nat → Int) (t : Nat) (hnn : ∀ e, e < t → -1 ≤ ell e)
    (h : 0 < Lbase ell t) : ∃ e, e < t ∧ ell e = Lbase ell t := by
  have hne : (List.range t).map (fun e => ell e) ≠ [] := by
    intro hc; unfold Lbase at h; rw [hc, List.foldr_nil] at h; omega
  have hmem : ((List.range t).map (fun e => ell e)).foldr max (-1)
      ∈ (List.range t).map (fun e => ell e) :=
    foldr_max_mem _ hne (fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [List.mem_range] at he
      exact hnn e he)
  rw [List.mem_map] at hmem
  obtain ⟨e, he, heq⟩ := hmem
  rw [List.mem_range] at he
  exact ⟨e, he, by unfold Lbase; exact heq⟩

theorem mem_latestList {ell : Nat → Int} {t : Nat} {lam : Int} {e : Nat} :
    (e : Int) ∈ latestList ell t lam ↔ e < t ∧ lam ≤ ell e := by
  unfold latestList
  rw [List.mem_map]
  constructor
  · rintro ⟨e', he', h⟩
    rw [List.mem_filter] at he'
    obtain ⟨hm, hp⟩ := he'
    rw [List.mem_range] at hm
    simp only [decide_eq_true_eq] at hp
    have : e' = e := by omega
    subst this; exact ⟨hm, hp⟩
  · rintro ⟨hm, h1⟩
    exact ⟨e, by rw [List.mem_filter]; exact ⟨by rw [List.mem_range]; exact hm, by simp [h1]⟩, rfl⟩

theorem le_latest {ell : Nat → Int} {t : Nat} {lam : Int} {e : Nat}
    (h : (e : Int) ∈ latestList ell t lam) : (e : Int) ≤ latest ell t lam :=
  le_foldr_max _ _ h

theorem latest_attained {ell : Nat → Int} {t : Nat} {lam : Int}
    (hne : latestList ell t lam ≠ []) :
    ∃ (e : Nat), (e : Int) = latest ell t lam ∧ e < t ∧ lam ≤ ell e := by
  have hmem : (latestList ell t lam).foldr max (-1) ∈ latestList ell t lam :=
    foldr_max_mem _ hne (fun x hx => by
      unfold latestList at hx
      rw [List.mem_map] at hx
      obtain ⟨e, _, hxe⟩ := hx
      rw [← hxe]; omega)
  unfold latestList at hmem
  rw [List.mem_map] at hmem
  obtain ⟨e, he, heq⟩ := hmem
  rw [List.mem_filter] at he
  obtain ⟨hm, hp⟩ := he
  rw [List.mem_range] at hm
  simp only [decide_eq_true_eq] at hp
  exact ⟨e, by unfold latest; exact heq, hm, hp⟩

/-- The closed-form `λ` for a non-future owner (`¬ t < u`). -/
theorem qcutLambda_eq {ell : Nat → Int} {t u : Nat} (htu : ¬ t < u) :
    qcutLambda ell t u = min (Lbase ell t) ((t : Int) - (u : Int)) := by
  unfold qcutLambda; rw [if_neg htu]

/-! ### Validity -/

theorem valid_qcutCand (ell : Nat → Int) (t u e : Nat) : Valid (qcutCand ell t u e) := by
  unfold qcutCand
  by_cases htu : t < u
  · rw [if_pos htu]; exact valid_mk _ _ (by omega)
  · rw [if_neg htu]; exact valid_mk _ _ (by omega)

theorem valid_baseRoute (ell : Nat → Int) (t : Nat) : Valid (baseRoute ell t) := by
  unfold baseRoute; exact valid_mk _ _ (by unfold latest; exact neg_one_le_foldr_max _)

theorem valid_bruteQCut (ell : Nat → Int) (t u : Nat) : Valid (bruteQCut ell t u) := by
  unfold bruteQCut
  by_cases htu : t < u
  · rw [if_pos htu]; exact valid_baseRoute ell t
  · rw [if_neg htu]
    apply valid_rmaxList
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨e, _, rfl⟩ := hr
    exact valid_qcutCand ell t u e

theorem valid_qcutClosed (ell : Nat → Int) (t u : Nat) : Valid (qcutClosed ell t u) := by
  unfold qcutClosed
  exact valid_mk _ _ (by unfold latest; exact neg_one_le_foldr_max _)

/-- The Q-cut length is capped by `t-u` — this is what makes an active repair
bridge beat the deletion baseline. -/
theorem bruteQCut_len_le (ell : Nat → Int) (t u : Nat) (hu : u ≤ t) :
    (bruteQCut ell t u).len ≤ (t : Int) - (u : Int) := by
  have htu : ¬ t < u := by omega
  unfold bruteQCut
  rw [if_neg htu]
  apply rmaxList_len_le
  · omega
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨e, _, rfl⟩ := hr
    unfold qcutCand
    rw [if_neg htu]
    unfold CutArith.mk
    by_cases h : min (ell e) ((t : Int) - (u : Int)) ≤ 0
    · rw [if_pos h]; simp only [Route.unmatched, Route.len]; omega
    · rw [if_neg h]; exact Int.min_le_right _ _

/-! ### The closed form is exact -/

theorem bruteQCut_le_qcutClosed (ell : Nat → Int) (t u : Nat) (hu : u ≤ t) :
    rle (bruteQCut ell t u) (qcutClosed ell t u) := by
  have htu : ¬ t < u := by omega
  unfold bruteQCut
  rw [if_neg htu]
  apply rmaxList_lub
  · exact valid_qcutClosed ell t u
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨e, he, rfl⟩ := hr
    rw [List.mem_range] at he
    have hleL : ell e ≤ Lbase ell t := le_Lbase ell t e he
    unfold qcutCand
    rw [if_neg htu]
    unfold qcutClosed
    by_cases hle : min (ell e) ((t : Int) - (u : Int)) ≤ 0
    · rw [mk_nonpos _ _ hle]; exact valid_rle_unmatched _ (valid_qcutClosed ell t u)
    · rw [mk_pos _ _ (by omega)]
      have hlam : 0 < qcutLambda ell t u := by rw [qcutLambda_eq htu]; omega
      rw [mk_pos _ _ hlam, qcutLambda_eq htu]
      unfold rle; dsimp only
      by_cases hlt : min (ell e) ((t : Int) - (u : Int))
          < min (Lbase ell t) ((t : Int) - (u : Int))
      · left; exact hlt
      · right
        refine ⟨by omega, ?_⟩
        apply le_latest
        rw [mem_latestList]
        refine ⟨he, ?_⟩
        have heq : min (ell e) ((t : Int) - (u : Int))
            = min (Lbase ell t) ((t : Int) - (u : Int)) := by omega
        rw [← heq]; exact Int.min_le_left _ _

theorem qcutClosed_le_bruteQCut (ell : Nat → Int) (t u : Nat) (hu : u ≤ t)
    (hnn : ∀ e, e < t → -1 ≤ ell e) :
    rle (qcutClosed ell t u) (bruteQCut ell t u) := by
  have htu : ¬ t < u := by omega
  have hLE := qcutLambda_eq (ell := ell) htu
  unfold qcutClosed
  by_cases hlam : qcutLambda ell t u ≤ 0
  · rw [mk_nonpos _ _ hlam]; exact valid_rle_unmatched _ (valid_bruteQCut ell t u)
  · rw [mk_pos _ _ (by omega)]
    have hLpos : 0 < Lbase ell t := by rw [hLE] at hlam; omega
    obtain ⟨e0, he0t, he0⟩ := Lbase_attained ell t hnn hLpos
    have hne : latestList ell t (qcutLambda ell t u) ≠ [] := by
      intro hc
      have hmem : (e0 : Int) ∈ latestList ell t (qcutLambda ell t u) := by
        rw [mem_latestList]
        refine ⟨he0t, ?_⟩
        rw [hLE]; omega
      rw [hc] at hmem; simp at hmem
    obtain ⟨e, heq, het, hle⟩ := latest_attained hne
    have hleL : ell e ≤ Lbase ell t := le_Lbase ell t e het
    unfold bruteQCut
    rw [if_neg htu]
    apply rle_rmaxList
    rw [List.mem_map]
    refine ⟨e, by rw [List.mem_range]; exact het, ?_⟩
    have heq1 : min (ell e) ((t : Int) - (u : Int)) = qcutLambda ell t u := by
      rw [hLE] at hle ⊢; omega
    have hc : 0 < (t : Int) - (u : Int) := by rw [hLE] at hlam; omega
    have hminpos : 0 < min (ell e) ((t : Int) - (u : Int)) := by omega
    unfold qcutCand
    rw [if_neg htu, mk_pos _ _ hminpos, heq1, heq]

theorem qcut_length_and_latest_endpoint (ell : Nat → Int) (t u : Nat) (hu : u ≤ t)
    (hnn : ∀ e, e < t → -1 ≤ ell e) :
    bruteQCut ell t u = qcutClosed ell t u :=
  rle_antisymm _ _ (bruteQCut_le_qcutClosed ell t u hu)
    (qcutClosed_le_bruteQCut ell t u hu hnn)

/-- **Future owner** (`t < u`): the owner is outside the query suffix, so the cut
is unconstrained and the route is the base route. -/
theorem qcut_future (ell : Nat → Int) (t u : Nat) (htu : t < u) :
    bruteQCut ell t u = qcutClosed ell t u := by
  have hb : bruteQCut ell t u = baseRoute ell t := by
    unfold bruteQCut; rw [if_pos htu]
  have hc : qcutClosed ell t u = baseRoute ell t := by
    simp only [qcutClosed, qcutLambda, baseRoute, if_pos htu]
  rw [hb, hc]

end QCut

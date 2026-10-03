import Std

/-!
## ROSA routes and their priority order

A `Route` is a `(len, endpoint)` pair.  ROSA's tie-break rules are:
larger `len` wins; on equal `len`, larger `endpoint` wins; every route of
length 0 is normalized to the unmatched route `(0, -1)`.
-/

structure Route where
  len : Int
  endpoint : Int
  deriving DecidableEq, Repr

namespace Route

@[ext] theorem ext {a b : Route} (h1 : a.len = b.len) (h2 : a.endpoint = b.endpoint) :
    a = b := by
  rcases a with ⟨la, ea⟩; rcases b with ⟨lb, eb⟩
  simp only at h1 h2
  rw [h1, h2]


/-- Validity invariant carried by every route we construct. -/
def Valid (r : Route) : Prop :=
  0 ≤ r.len ∧ -1 ≤ r.endpoint ∧ (r.len = 0 → r.endpoint = -1)

/-- The canonical unmatched route `(0, -1)`. -/
def unmatched : Route := ⟨0, -1⟩

theorem valid_unmatched : Valid unmatched := by
  unfold Valid unmatched; simp

/-- ROSA priority: larger length wins; ties broken by larger endpoint. -/
def rle (a b : Route) : Prop :=
  a.len < b.len ∨ (a.len = b.len ∧ a.endpoint ≤ b.endpoint)

instance (a b : Route) : Decidable (rle a b) := by
  unfold rle; infer_instance

theorem rle_refl (a : Route) : rle a a := by
  rcases a with ⟨l, e⟩; unfold rle; omega

theorem rle_total (a b : Route) : rle a b ∨ rle b a := by
  rcases a with ⟨la, ea⟩; rcases b with ⟨lb, eb⟩
  unfold rle; dsimp only; omega

theorem rle_trans (a b c : Route) (hab : rle a b) (hbc : rle b c) : rle a c := by
  rcases a with ⟨la, ea⟩; rcases b with ⟨lb, eb⟩; rcases c with ⟨lc, ec⟩
  unfold rle at *; dsimp only at *; omega

theorem rle_antisymm (a b : Route) (hab : rle a b) (hba : rle b a) : a = b := by
  rcases a with ⟨la, ea⟩; rcases b with ⟨lb, eb⟩
  unfold rle at hab hba; dsimp only at hab hba
  have h1 : la = lb := by omega
  have h2 : ea = eb := by omega
  subst h1; subst h2; rfl

theorem valid_rle_unmatched (x : Route) (h : Valid x) : rle unmatched x := by
  rcases x with ⟨l, e⟩
  unfold Valid at h; dsimp only at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold rle unmatched; dsimp only
  omega

/-- Priority max. -/
def rmax (a b : Route) : Route := if rle a b then b else a

theorem rle_rmax_left (a b : Route) : rle a (rmax a b) := by
  unfold rmax
  by_cases h : rle a b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact rle_refl a

theorem rle_rmax_right (a b : Route) : rle b (rmax a b) := by
  unfold rmax
  by_cases h : rle a b
  · rw [if_pos h]; exact rle_refl b
  · rw [if_neg h]
    rcases rle_total a b with hab | hba
    · exact absurd hab h
    · exact hba

theorem rle_rmax_lub (a b c : Route) : rle (rmax a b) c ↔ rle a c ∧ rle b c := by
  constructor
  · intro h
    exact ⟨rle_trans a (rmax a b) c (rle_rmax_left a b) h,
           rle_trans b (rmax a b) c (rle_rmax_right a b) h⟩
  · intro h
    unfold rmax
    by_cases hab : rle a b
    · rw [if_pos hab]; exact h.2
    · rw [if_neg hab]; exact h.1

theorem valid_rmax (a b : Route) (ha : Valid a) (hb : Valid b) : Valid (rmax a b) := by
  unfold rmax
  by_cases h : rle a b
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact ha

/-- `rmax` is commutative. -/
theorem rmax_comm (a b : Route) : rmax a b = rmax b a := by
  apply rle_antisymm
  · exact (rle_rmax_lub a b (rmax b a)).mpr ⟨rle_rmax_right b a, rle_rmax_left b a⟩
  · exact (rle_rmax_lub b a (rmax a b)).mpr ⟨rle_rmax_right a b, rle_rmax_left a b⟩

/-- `rmax` is associative. -/
theorem rmax_assoc (a b c : Route) : rmax (rmax a b) c = rmax a (rmax b c) := by
  apply rle_antisymm
  · exact (rle_rmax_lub (rmax a b) c (rmax a (rmax b c))).mpr
      ⟨(rle_rmax_lub a b (rmax a (rmax b c))).mpr
        ⟨rle_rmax_left a (rmax b c),
         rle_trans b (rmax b c) _ (rle_rmax_left b c) (rle_rmax_right a (rmax b c))⟩,
       rle_trans c (rmax b c) _ (rle_rmax_right b c) (rle_rmax_right a (rmax b c))⟩
  · exact (rle_rmax_lub a (rmax b c) (rmax (rmax a b) c)).mpr
      ⟨rle_trans a (rmax a b) _ (rle_rmax_left a b) (rle_rmax_left (rmax a b) c),
       (rle_rmax_lub b c (rmax (rmax a b) c)).mpr
        ⟨rle_trans b (rmax a b) _ (rle_rmax_right a b) (rle_rmax_left (rmax a b) c),
         rle_rmax_right (rmax a b) c⟩⟩

/-- The unmatched route is the identity of `rmax` on valid routes. -/
theorem rmax_unmatched_right (x : Route) (hx : Valid x) : rmax x unmatched = x := by
  apply rle_antisymm
  · exact (rle_rmax_lub x unmatched x).mpr ⟨rle_refl x, valid_rle_unmatched x hx⟩
  · exact rle_rmax_left x unmatched

theorem rmax_unmatched_left (x : Route) (hx : Valid x) : rmax unmatched x = x := by
  rw [rmax_comm]; exact rmax_unmatched_right x hx

theorem rmax_len_le (a b : Route) : (rmax a b).len ≤ max a.len b.len := by
  unfold rmax
  by_cases h : rle a b
  · rw [if_pos h]; exact Int.le_max_right _ _
  · rw [if_neg h]; exact Int.le_max_left _ _

/-- Fold max over a list, seeded with the unmatched route. -/
def rmaxList : List Route → Route
  | [] => unmatched
  | r :: rs => rmax r (rmaxList rs)

theorem rle_rmaxList (r : Route) (l : List Route) (hr : r ∈ l) : rle r (rmaxList l) := by
  induction l with
  | nil => simp at hr
  | cons x xs ih =>
    rw [rmaxList]
    rcases List.mem_cons.mp hr with h | h
    · subst h; exact rle_rmax_left _ _
    · exact rle_trans _ _ _ (ih h) (rle_rmax_right _ _)

theorem rmaxList_lub (l : List Route) (x : Route) (hx : Valid x)
    (h : ∀ r ∈ l, rle r x) : rle (rmaxList l) x := by
  induction l with
  | nil => simp only [rmaxList]; exact valid_rle_unmatched x hx
  | cons y ys ih =>
    rw [rmaxList]
    apply (rle_rmax_lub y (rmaxList ys) x).mpr
    exact ⟨h y (by simp), ih (fun r hr => h r (by simp [hr]))⟩

theorem rmaxList_len_le (l : List Route) (c : Int) (hc : 0 ≤ c)
    (h : ∀ r ∈ l, r.len ≤ c) : (rmaxList l).len ≤ c := by
  induction l with
  | nil => simp only [rmaxList, unmatched]; exact hc
  | cons y ys ih =>
    rw [rmaxList]
    have h1 : y.len ≤ c := h y (by simp)
    have h2 : (rmaxList ys).len ≤ c := ih (fun r hr => h r (by simp [hr]))
    have := rmax_len_le y (rmaxList ys)
    omega

theorem valid_rmaxList (l : List Route) (h : ∀ r ∈ l, Valid r) : Valid (rmaxList l) := by
  induction l with
  | nil => simp only [rmaxList]; exact valid_unmatched
  | cons y ys ih =>
    rw [rmaxList]
    exact valid_rmax y (rmaxList ys) (h y (by simp))
      (ih (fun r hr => h r (by simp [hr])))

/-- `rmaxList` is a homomorphism for `++` (seeded by `unmatched`). -/
theorem rmaxList_append (l₁ l₂ : List Route) (h₂ : ∀ r ∈ l₂, Valid r) :
    rmaxList (l₁ ++ l₂) = rmax (rmaxList l₁) (rmaxList l₂) := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append]
    rw [rmax_comm]
    exact (rmax_unmatched_right _ (valid_rmaxList l₂ h₂)).symm
  | cons x xs ih =>
    simp only [List.cons_append, rmaxList]
    rw [ih]
    exact (rmax_assoc x (rmaxList xs) (rmaxList l₂)).symm

end Route

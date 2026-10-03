import Std
import Route
import Lcs
import RunRectangle
import Repair
import RosBridge
import OwnerBridges
import Interior
import OwnerCompress
import OwnerCorrect

/-!
## Phase H (new) — step 11-K: the K-side compression is exact

`field (kOwnerCompressed …) t = field (Actual) t`.  For a strict-interior K-owner
`u` the strict-interior Q-centres (`a<p<b`) are *replaced* by the single
constant-route candidate `kInteriorBulk a b u` (§8): each such bridge is active
only at `t=p` with value `(1,u)`.  String-free; reuses `OwnerCorrect`'s lemmas.
-/

namespace OwnerCorrectK
open Route Lcs RunRect Repair RosBridge OwnerBridges OwnerCompress OwnerCorrect

/-- The constant route the K-side interior bulk contributes at `t`. -/
def bulkRoute (a b u t : Nat) : Route :=
  if max (a + 1) (u + 1) ≤ t ∧ t ≤ b - 1 then (⟨1, (u : Int)⟩ : Route) else unmatched

theorem route_one_valid (u : Nat) : Valid (⟨1, (u : Int)⟩ : Route) := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : Int) ≤ 1; omega
  · show (-1 : Int) ≤ (u : Int)
    have h : (0 : Int) ≤ (u : Int) := Int.natCast_nonneg u
    omega
  · show (1 : Int) = 0 → (u : Int) = -1
    intro h; omega

theorem bulkRoute_valid (a b u t : Nat) : Valid (bulkRoute a b u t) := by
  unfold bulkRoute; split
  · exact route_one_valid u
  · exact valid_unmatched

/-- `rmax x unmatched = x` for valid `x`. -/
theorem rmax_unmatched_right (x : Route) (hx : Valid x) : rmax x unmatched = x := by
  unfold rmax
  by_cases h : rle x unmatched
  · rw [if_pos h, rle_antisymm x unmatched h (valid_rle_unmatched x hx)]
  · rw [if_neg h]

/-- `field` of the single bulk candidate is `bulkRoute`. -/
theorem field_kInteriorBulk (a b u t : Nat) :
    field [kInteriorBulk a b u] t = bulkRoute a b u t := by
  unfold field kInteriorBulk bulkRoute
  simp only [List.map_cons, List.map_nil, rmaxList]
  split
  · exact rmax_unmatched_right _ (route_one_valid u)
  · exact rmax_unmatched_right _ valid_unmatched

/-! ### The dropped family -/

theorem kOwnerDropped_mem {α : Type} [DecidableEq α] {q k : Nat → α} {Tq Tk a b c d u : Nat}
    {x : Bridge} :
    x ∈ kOwnerDropped q k Tq Tk a b c d u ↔
      x ∈ kOwnerBridges q k Tq Tk a b c d u ∧ kOwnerKept a b c d u x = false := by
  unfold kOwnerDropped
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simp [h2]⟩

private theorem dropped_interior {α : Type} [DecidableEq α] {q k : Nat → α}
    {Tq Tk a b c d u : Nat} {x : Bridge}
    (hx : x ∈ kOwnerBridges q k Tq Tk a b c d u) (hk : kOwnerKept a b c d u x = false) :
    a < x.p ∧ x.p < b ∧ c < x.u ∧ x.u < d := by
  have hxu : x.u = u := kOwnerBridges_u hx
  have hcore : a < x.p ∧ x.p < b ∧ c < u ∧ u < d := by
    apply Classical.byContradiction
    intro hc
    exact (show ¬ (kOwnerKept a b c d u x = true) from by rw [hk]; simp)
      ((kOwnerKept_eq a b c d u x).mpr hc)
  exact ⟨hcore.1, hcore.2.1, by rw [hxu]; exact hcore.2.2.1, by rw [hxu]; exact hcore.2.2.2⟩

/-- A dropped K-owner bridge is active only at its birth `p`, where it contributes
`(1,u)`. -/
theorem bval_dropped {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    [DecidableEq α] (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) {x : Bridge} (hx : x ∈ kOwnerBridges q k Tq Tk a b c d u)
    (hk : kOwnerKept a b c d u x = false) (t : Nat) :
    bval x t = (if t = x.p then (⟨1, (u : Int)⟩ : Route) else unmatched) := by
  obtain ⟨h1, h2, h3, h4⟩ := dropped_interior hx hk
  obtain ⟨-, -, p₀, hap, hpb, hup, hxu⟩ := mem_kOwnerBridges.mp hx
  simp only [hxu, mkBridge_p, mkBridge_u] at h1 h2 h3 h4
  have hkey := mkBridge_strict_interior hQ hK hne h1 h2 h3 h4
  have hact : ∀ s, x.Active s ↔ s = x.p := by rw [hxu]; exact hkey.2.2
  have hrt : x.routeAt x.p = (⟨1, (u : Int)⟩ : Route) := by rw [hxu]; exact hkey.2.1
  unfold bval
  by_cases ht : t = x.p
  · rw [if_pos ((hact t).mpr ht), ht, if_pos rfl]; exact hrt
  · rw [if_neg (by rw [hact]; exact ht), if_neg ht]

/-- A dropped bridge is dominated by the bulk route at every `t`. -/
theorem bval_le_bulkRoute {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    [DecidableEq α] (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) {x : Bridge} (hx : x ∈ kOwnerBridges q k Tq Tk a b c d u)
    (hk : kOwnerKept a b c d u x = false) (t : Nat) :
    rle (bval x t) (bulkRoute a b u t) := by
  rw [bval_dropped hQ hK hne hx hk t]
  obtain ⟨h1, h2, h3, h4⟩ := dropped_interior hx hk
  obtain ⟨-, -, p₀, hap, hpb, hup, hxu⟩ := mem_kOwnerBridges.mp hx
  simp only [hxu, mkBridge_p, mkBridge_u] at h1 h2 h3 h4
  have hlo : max (a + 1) (u + 1) ≤ x.p := by rw [hxu]; simp only [mkBridge_p]; omega
  have hhi : x.p ≤ b - 1 := by rw [hxu]; simp only [mkBridge_p]; omega
  unfold bulkRoute
  by_cases ht : t = x.p
  · rw [if_pos ht, if_pos (by omega)]; exact rle_refl _
  · rw [if_neg ht]
    by_cases hh : max (a + 1) (u + 1) ≤ t ∧ t ≤ b - 1
    · rw [if_pos hh]; exact valid_rle_unmatched _ (route_one_valid u)
    · rw [if_neg hh]; exact rle_refl _

/-- The bulk route is dominated by the actual field. -/
theorem bulkRoute_le_field {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    [DecidableEq α] (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hcu : c < u) (hud : u < d) (t : Nat) :
    rle (bulkRoute a b u t) (fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t) := by
  unfold bulkRoute
  by_cases h : max (a + 1) (u + 1) ≤ t ∧ t ≤ b - 1
  · rw [if_pos h]
    have hmem : mkBridge q k Tq Tk t u ∈ kOwnerBridges q k Tq Tk a b c d u := by
      rw [mem_kOwnerBridges]
      exact ⟨by omega, by omega, t, by omega, by omega, by omega, rfl⟩
    have hstrict : a < t ∧ t < b ∧ c < u ∧ u < d :=
      ⟨by omega, by omega, hcu, hud⟩
    have hkept : kOwnerKept a b c d u (mkBridge q k Tq Tk t u) = false := by
      cases hb : kOwnerKept a b c d u (mkBridge q k Tq Tk t u)
      · rfl
      · exact absurd hstrict ((kOwnerKept_eq a b c d u _).mp hb)
    have hb0 := bval_dropped hQ hK hne hmem hkept t
    rw [mkBridge_p, if_pos rfl] at hb0
    rw [← hb0]
    exact rle_fieldBridges_of_mem hmem t
  · rw [if_neg h]
    exact valid_rle_unmatched _ (fieldBridges_valid _ _)

/-! ### step 11-K: the main theorem -/

theorem kOwnerCompressed_field {q k : Nat → α} {Tq Tk a b c d u : Nat} {αs βs : α}
    [DecidableEq α] (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) (hcu : c < u) (hud : u < d) :
    ∀ t, field (kOwnerCompressed q k Tq Tk a b c d u) t
           = fieldBridges (kOwnerBridges q k Tq Tk a b c d u) t := by
  intro t
  have hcomp : field (kOwnerCompressed q k Tq Tk a b c d u) t
      = rmax (bulkRoute a b u t)
          (rmaxList ((kOwnerKeptList q k Tq Tk a b c d u).map (fun b => bval b t))) := by
    unfold field kOwnerCompressed
    rw [if_pos ⟨hcu, hud⟩, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.singleton_append, rmaxList]
    rfl
  rw [hcomp]
  apply rle_antisymm
  · -- rmax(bulk, kept) ≤ actual
    apply (rle_rmax_lub _ _ _).mpr
    refine ⟨bulkRoute_le_field hQ hK hne hcu hud t, ?_⟩
    apply rmaxList_lub _ _ (fieldBridges_valid _ _)
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact rle_fieldBridges_of_mem (List.mem_filter.mp hx).1 t
  · -- actual ≤ rmax(bulk, kept)
    apply rmaxList_lub _ _ (by
      unfold rmax; split
      · exact fieldBridges_valid _ _
      · exact bulkRoute_valid a b u t)
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    by_cases hk : kOwnerKept a b c d u x = true
    · exact rle_trans _ _ _ (rle_fieldBridges_of_mem (List.mem_filter.mpr ⟨hx, hk⟩) t)
        (rle_rmax_right (bulkRoute a b u t)
          (rmaxList ((kOwnerKeptList q k Tq Tk a b c d u).map (fun b => bval b t))))
    · have hkf : kOwnerKept a b c d u x = false := by
        cases hv : kOwnerKept a b c d u x <;> simp_all
      exact rle_trans _ _ _ (bval_le_bulkRoute hQ hK hne hx hkf t)
        (rle_rmax_left (bulkRoute a b u t)
          (rmaxList ((kOwnerKeptList q k Tq Tk a b c d u).map (fun b => bval b t))))

end OwnerCorrectK

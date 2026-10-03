import Std
import Route
import Lcs
import RunRectangle
import Repair
import RosBridge
import OwnerBridges
import Interior
import OwnerCompress

/-!
## Phase H (new) — step 11-Q: the Q-side compression is exact

`field (qOwnerCompressed …) t = field (Actual) t`.  When `p` is a strict-interior
Q-owner (`a<p<b`) every strict-interior K-centre has `L=R=0`, is active only at
`t=p` and contributes `(1,u)`; they collapse to `u_* = min(d-1,p-1)`.  When
`¬(a<p<b)` there is no collapse.  String-free plumbing on σ (§1) plus the
already-proved `repair_strict_interior_trivial`.
-/

namespace OwnerCorrect
open Route Lcs RunRect Repair RosBridge OwnerBridges OwnerCompress

/-- The value a bridge contributes at `t` (unmatched when inactive). -/
def bval (b : Bridge) (t : Nat) : Route := if b.Active t then b.routeAt t else unmatched

theorem bval_valid (b : Bridge) (t : Nat) : Valid (bval b t) := by
  unfold bval; split
  · exact Bridge.valid_routeAt _ _ ‹_›
  · exact valid_unmatched

/-- **step 11 interface**: `field` on a bridge list is `fieldBridges`. -/
theorem field_candsOf (bs : List Bridge) (t : Nat) :
    field (candsOf bs) t = fieldBridges bs t := by
  unfold field fieldBridges candsOf
  rw [List.map_map]
  exact congrArg rmaxList (List.map_congr_left (fun b _ => rfl))

theorem fieldBridges_valid (bs : List Bridge) (t : Nat) : Valid (fieldBridges bs t) := by
  unfold fieldBridges
  apply valid_rmaxList
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨b, _, rfl⟩ := hr
  exact bval_valid b t

/-- Every member is dominated by the field. -/
theorem rle_fieldBridges_of_mem {bs : List Bridge} {b : Bridge} (hb : b ∈ bs) (t : Nat) :
    rle (bval b t) (fieldBridges bs t) := by
  unfold fieldBridges bval
  apply rle_rmaxList
  rw [List.mem_map]
  exact ⟨b, hb, rfl⟩

/-- **Dropping dominated members does not change the field.** -/
theorem fieldBridges_filter_eq {bs : List Bridge} (pr : Bridge → Bool) (t : Nat)
    (h : ∀ b ∈ bs, pr b = false → rle (bval b t) (fieldBridges (bs.filter pr) t)) :
    fieldBridges (bs.filter pr) t = fieldBridges bs t := by
  apply rle_antisymm
  · apply rmaxList_lub _ _ (fieldBridges_valid bs t)
    intro r hr
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    exact rle_fieldBridges_of_mem (List.mem_filter.mp hb).1 t
  · apply rmaxList_lub _ _ (fieldBridges_valid (bs.filter pr) t)
    intro r hr
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    by_cases hp : pr b = true
    · exact rle_fieldBridges_of_mem (List.mem_filter.mpr ⟨hb, hp⟩) t
    · have hpf : pr b = false := by cases hpb : pr b <;> simp_all
      exact h b hb hpf

/-! ### Strict-interior bridge facts -/

/-- A strict-interior `mkBridge` has `R = 0`, contributes `(1,u)` at `p`, and is
active only at `t = p`. -/
theorem mkBridge_strict_interior {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    [DecidableEq α] (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) {p u : Nat} (hap : a < p) (hpb : p < b) (huc : c < u) (hud : u < d) :
    (mkBridge q k Tq Tk p u).R = 0
      ∧ (mkBridge q k Tq Tk p u).routeAt p = (⟨1, (u : Int)⟩ : Route)
      ∧ ∀ t, (mkBridge q k Tq Tk p u).Active t ↔ t = p := by
  obtain ⟨hL, hR⟩ := repair_strict_interior_trivial hQ hK hne hap hpb huc hud
  have hp0 : 0 < p := by omega
  have hu0 : 0 < u := by omega
  have hLc : leftCtx q k p u = 0 := by rw [leftCtx_eq hp0 hu0, hL]
  have hRc : rightCtx q k Tq Tk p u = 0 := by unfold rightCtx; exact hR
  refine ⟨hRc, ?_, ?_⟩
  · show (⟨((leftCtx q k p u + 1 + (p - p) : Nat) : Int),
        ((u + (p - p) : Nat) : Int)⟩ : Route) = (⟨1, (u : Int)⟩ : Route)
    have h1' : leftCtx q k p u + 1 + (p - p) = 1 := by omega
    have h2' : u + (p - p) = u := by omega
    rw [h1', h2', Int.ofNat_one]
  · intro t
    show p ≤ t ∧ t ≤ p + rightCtx q k Tq Tk p u ↔ t = p
    rw [hRc]; omega

/-! ### The Q-side domination relation -/

/-- **step 11-Q key lemma.**  A dropped Q-owner bridge (a strict-interior K-centre
`u ≠ u_*`) is dominated at every `t` by the kept `u_*` bridge. -/
theorem qOwner_dominated {q k : Nat → α} {Tq Tk a b c d p : Nat} {αs βs : α}
    [DecidableEq α] (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) {t : Nat} {y : Bridge}
    (hy : y ∈ qOwnerBridges q k Tq Tk a b c d p)
    (hk : qOwnerKept a b c d p y = false) :
    rle (bval y t)
      (fieldBridges ((qOwnerBridges q k Tq Tk a b c d p).filter (qOwnerKept a b c d p)) t) := by
  have hinter : a < p ∧ p < b ∧ c < y.u ∧ y.u < d ∧ y.u ≠ min (d - 1) (p - 1) := by
    apply Classical.byContradiction
    intro hc
    exact (show ¬ (qOwnerKept a b c d p y = true) from by rw [hk]; simp)
      ((qOwnerKept_eq a b c d p y).mpr hc)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinter
  obtain ⟨-, -, u, hcu, hud, hup, hyu⟩ := mem_qOwnerBridges.mp hy
  have huy : y.u = u := by rw [hyu]; rfl
  have huc' : c < u := by rw [← huy]; exact h3
  have hud' : u < d := by rw [← huy]; exact h4
  have hup' : u < p := hup
  have hyR : y.R = 0 := by
    rw [hyu]; exact (mkBridge_strict_interior hQ hK hne h1 h2 huc' hud').1
  have hyrt : y.routeAt p = (⟨1, (y.u : Int)⟩ : Route) := by
    rw [hyu]; exact (mkBridge_strict_interior hQ hK hne h1 h2 huc' hud').2.1
  have hyact : ∀ t, y.Active t ↔ t = p := by
    rw [hyu]; exact (mkBridge_strict_interior hQ hK hne h1 h2 huc' hud').2.2
  have hut : y.u ≤ min (d - 1) (p - 1) := by omega
  have hcstar : c < min (d - 1) (p - 1) := by omega
  have hdstar : min (d - 1) (p - 1) < d := by omega
  have hpstar : min (d - 1) (p - 1) < p := by omega
  have hy'act : ∀ t, (mkBridge q k Tq Tk p (min (d - 1) (p - 1))).Active t ↔ t = p :=
    (mkBridge_strict_interior hQ hK hne h1 h2 hcstar hdstar).2.2
  have hy'rt : (mkBridge q k Tq Tk p (min (d - 1) (p - 1))).routeAt p
      = (⟨1, ((min (d - 1) (p - 1) : Nat) : Int)⟩ : Route) :=
    (mkBridge_strict_interior hQ hK hne h1 h2 hcstar hdstar).2.1
  have hmem' : mkBridge q k Tq Tk p (min (d - 1) (p - 1))
      ∈ (qOwnerBridges q k Tq Tk a b c d p).filter (qOwnerKept a b c d p) := by
    rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_qOwnerBridges]
      exact ⟨(by omega : a ≤ p), (by omega : p ≤ b), min (d - 1) (p - 1),
        (by omega : c ≤ min (d - 1) (p - 1)), (by omega : min (d - 1) (p - 1) ≤ d),
        hpstar, rfl⟩
    · rw [qOwnerKept_eq]
      intro hc; exact hc.2.2.2.2 rfl
  have hdom : rle (bval y t) (bval (mkBridge q k Tq Tk p (min (d - 1) (p - 1))) t) := by
    unfold bval
    by_cases ht : t = p
    · have hrt : y.routeAt t = (⟨1, (y.u : Int)⟩ : Route) := by rw [ht]; exact hyrt
      have hrt' : (mkBridge q k Tq Tk p (min (d - 1) (p - 1))).routeAt t
          = (⟨1, ((min (d - 1) (p - 1) : Nat) : Int)⟩ : Route) := by rw [ht]; exact hy'rt
      rw [if_pos ((hyact t).mpr ht), if_pos ((hy'act t).mpr ht), hrt, hrt']
      unfold rle
      exact Or.inr ⟨rfl, Int.ofNat_le.mpr hut⟩
    · have hna : ¬ y.Active t := by rw [hyact]; exact ht
      rw [if_neg hna]
      exact valid_rle_unmatched _ (bval_valid _ _)
  exact rle_trans _ _ _ hdom (rle_fieldBridges_of_mem hmem' t)

/-! ### step 11-Q: the main theorem -/

/-- **step 11-Q.**  The Q-side compressed candidate field equals the actual one,
for every `t`. -/
theorem qOwnerCompressed_field {q k : Nat → α} {Tq Tk a b c d p : Nat} {αs βs : α}
    [DecidableEq α] (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) :
    ∀ t, field (qOwnerCompressed q k Tq Tk a b c d p) t
           = fieldBridges (qOwnerBridges q k Tq Tk a b c d p) t := by
  intro t
  rw [show qOwnerCompressed q k Tq Tk a b c d p
        = candsOf ((qOwnerBridges q k Tq Tk a b c d p).filter (qOwnerKept a b c d p))
      from rfl, field_candsOf]
  exact fieldBridges_filter_eq (qOwnerKept a b c d p) t
    (fun b hb hk => qOwner_dominated hQ hK hne hb hk)

end OwnerCorrect

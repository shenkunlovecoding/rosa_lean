import Std
import Route
import OwnerBridges
import OwnerCompress
import OwnerCorrect
import OwnerCorrectK

/-!
## Phase H — §11.1: `O(1)` winner pieces, both sides

* **exact candidate bound** (§20): the strict-interior compressed list has `≤ 3`
  elements — interior bulk (1) + the two run-edge centres.
* **Q-side winner** (§11.1): the winner route is exactly the max of those three
  explicit slots ⇒ `O(1)` pieces.

All Std-only (no Mathlib needed: `List.Nodup.length_le_of_subset` etc. are Std).
-/

namespace WinnerPieces
open Route Lcs Repair RosBridge OwnerBridges OwnerCompress OwnerCorrect OwnerCorrectK

/-! ### List helpers -/

/-- `map` preserves `Nodup` under an injective function. -/
theorem nodup_map_of_injective {αs βs : Type} {f : αs → βs}
    (hf : ∀ a b, f a = f b → a = b) {l : List αs} (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (List.nodup_cons.mp h).2⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨b, hb, hba⟩ := hmem
    exact (List.nodup_cons.mp h).1 (by rw [← hf b a hba]; exact hb)

theorem mkBridge_u_inj {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk p : Nat) :
    ∀ u u' : Nat, mkBridge q k Tq Tk p u = mkBridge q k Tq Tk p u' → u = u' := by
  intro u u' h
  have := congrArg (fun b : Bridge => b.u) h
  simpa using this

theorem mkBridge_p_inj {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk u : Nat) :
    ∀ p p' : Nat, mkBridge q k Tq Tk p u = mkBridge q k Tq Tk p' u → p = p' := by
  intro p p' h
  have := congrArg (fun b : Bridge => b.p) h
  simpa using this

theorem qOwnerBridges_nodup {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d p : Nat) :
    (qOwnerBridges q k Tq Tk a b c d p).Nodup := by
  unfold qOwnerBridges
  by_cases h : a ≤ p ∧ p ≤ b
  · rw [if_pos h]
    exact nodup_map_of_injective (mkBridge_u_inj q k Tq Tk p)
      (List.Nodup.sublist (List.filter_sublist (p := fun u => decide (c ≤ u ∧ u ≤ d ∧ u < p)))
        List.nodup_range)
  · rw [if_neg h]; exact List.nodup_nil

theorem kOwnerBridges_nodup {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d u : Nat) :
    (kOwnerBridges q k Tq Tk a b c d u).Nodup := by
  unfold kOwnerBridges
  by_cases h : c ≤ u ∧ u ≤ d
  · rw [if_pos h]
    exact nodup_map_of_injective (mkBridge_p_inj q k Tq Tk u)
      (List.Nodup.sublist (List.filter_sublist (p := fun p => decide (a ≤ p ∧ p ≤ b ∧ u < p)))
        List.nodup_range)
  · rw [if_neg h]; exact List.nodup_nil

/-! ### The live kept-centre lists -/

abbrev QKept {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d p : Nat) : List Bridge :=
  (qOwnerBridges q k Tq Tk a b c d p).filter (qOwnerKept a b c d p)

abbrev KKept {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d u : Nat) : List Bridge :=
  kOwnerKeptList q k Tq Tk a b c d u

/-- Every live kept Q-centre is one of the three slots (`c`, `d`, `u_*`). -/
theorem qOwner_filter_subset {α : Type} [DecidableEq α] (q k : Nat → α)
    (Tq Tk a b c d p : Nat) (h1 : a < p) (h2 : p < b) :
    QKept q k Tq Tk a b c d p
      ⊆ [mkBridge q k Tq Tk p c, mkBridge q k Tq Tk p d,
         mkBridge q k Tq Tk p (min (d - 1) (p - 1))] := by
  intro x hx
  rw [List.mem_filter] at hx
  obtain ⟨hxob, hxk⟩ := hx
  obtain ⟨-, -, u, hcu, hud, hup, rfl⟩ := mem_qOwnerBridges.mp hxob
  rw [qOwnerKept_eq] at hxk
  simp only [mkBridge_p, mkBridge_u] at hxk
  have hnu : ¬(c < u ∧ u < d ∧ u ≠ min (d - 1) (p - 1)) :=
    fun hc => hxk ⟨h1, h2, hc.1, hc.2.1, hc.2.2⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  by_cases he : u = min (d - 1) (p - 1)
  · exact Or.inr (Or.inr (by rw [he]))
  · have hcd : ¬(c < u ∧ u < d) := fun hc => hnu ⟨hc.1, hc.2, he⟩
    by_cases hclt : c < u
    · exact Or.inr (Or.inl (by
        have : ¬(u < d) := fun hlt => hcd ⟨hclt, hlt⟩
        rw [show u = d by omega]))
    · exact Or.inl (by rw [show u = c by omega])

/-- Every live kept K-centre is one of the two edge slots (`a`, `b`). -/
theorem kOwner_filter_subset {α : Type} [DecidableEq α] (q k : Nat → α)
    (Tq Tk a b c d u : Nat) (h1 : c < u) (h2 : u < d) :
    KKept q k Tq Tk a b c d u ⊆ [mkBridge q k Tq Tk a u, mkBridge q k Tq Tk b u] := by
  intro x hx
  unfold KKept kOwnerKeptList at hx
  rw [List.mem_filter] at hx
  obtain ⟨hxob, hxk⟩ := hx
  obtain ⟨-, -, p₀, hap, hpb, hup, rfl⟩ := mem_kOwnerBridges.mp hxob
  rw [kOwnerKept_eq] at hxk
  simp only [mkBridge_p, mkBridge_u] at hxk
  have hpab : ¬(a < p₀ ∧ p₀ < b) := fun hc => hxk ⟨hc.1, hc.2, h1, h2⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  by_cases hat : a < p₀
  · exact Or.inr (by
      have : ¬(p₀ < b) := fun hlt => hpab ⟨hat, hlt⟩
      rw [show p₀ = b by omega])
  · exact Or.inl (by rw [show p₀ = a by omega])

/-! ### §20 exact candidate bounds -/

/-- **§20 exact bound (Q side).**  A strict-interior Q-owner's compressed list has
at most three elements. -/
theorem qOwnerCompressed_length_le_three {α : Type} [DecidableEq α] (q k : Nat → α)
    {Tq Tk a b c d p : Nat} (h1 : a < p) (h2 : p < b) :
    (qOwnerCompressed q k Tq Tk a b c d p).length ≤ 3 := by
  have hlen : (qOwnerCompressed q k Tq Tk a b c d p).length
      = (QKept q k Tq Tk a b c d p).length := by
    unfold qOwnerCompressed QKept; rw [List.length_map]
  rw [hlen]
  have hnod : (QKept q k Tq Tk a b c d p).Nodup :=
    List.Nodup.sublist (List.filter_sublist (p := qOwnerKept a b c d p))
      (qOwnerBridges_nodup q k Tq Tk a b c d p)
  have := List.Nodup.length_le_of_subset hnod (qOwner_filter_subset q k Tq Tk a b c d p h1 h2)
  simpa using this

/-- **§20 exact bound (K side).**  A strict-interior K-owner's compressed list has
at most three elements. -/
theorem kOwnerCompressed_length_le_three {α : Type} [DecidableEq α] (q k : Nat → α)
    {Tq Tk a b c d u : Nat} (h1 : c < u) (h2 : u < d) :
    (kOwnerCompressed q k Tq Tk a b c d u).length ≤ 3 := by
  have hmain : (kOwnerCompressed q k Tq Tk a b c d u).length
      = 1 + (KKept q k Tq Tk a b c d u).length := by
    unfold kOwnerCompressed KKept kOwnerKeptList
    rw [if_pos ⟨h1, h2⟩, List.length_append, List.length_map]
    simp only [List.length_cons, List.length_nil]
  rw [hmain]
  have hnod : (KKept q k Tq Tk a b c d u).Nodup := by
    unfold KKept kOwnerKeptList
    exact List.Nodup.sublist (List.filter_sublist (p := kOwnerKept a b c d u))
      (kOwnerBridges_nodup q k Tq Tk a b c d u)
  have := List.Nodup.length_le_of_subset hnod (kOwner_filter_subset q k Tq Tk a b c d u h1 h2)
  simp only [List.length_cons, List.length_nil] at this
  omega

/-! ### §11.1 — Q-side winner is one of at most three slot contributions -/

/-- A slot's contribution at `t` (`unmatched` when the slot is not a live kept centre). -/
def qSlot {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d p u : Nat) (t : Nat) : Route :=
  if mkBridge q k Tq Tk p u ∈ QKept q k Tq Tk a b c d p then bval (mkBridge q k Tq Tk p u) t
  else unmatched

theorem qSlot_valid {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d p u t : Nat) :
    Valid (qSlot q k Tq Tk a b c d p u t) := by
  unfold qSlot; split
  · exact bval_valid _ _
  · exact valid_unmatched

theorem qSlot_eq_bval {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d p u : Nat)
    (hx : mkBridge q k Tq Tk p u ∈ QKept q k Tq Tk a b c d p) (t : Nat) :
    qSlot q k Tq Tk a b c d p u t = bval (mkBridge q k Tq Tk p u) t := by
  unfold qSlot; rw [if_pos hx]

theorem qSlot_eq_unmatched {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d p u : Nat)
    (hx : mkBridge q k Tq Tk p u ∉ QKept q k Tq Tk a b c d p) (t : Nat) :
    qSlot q k Tq Tk a b c d p u t = unmatched := by
  unfold qSlot; rw [if_neg hx]

/-- **§11.1 (Q side).**  For a strict-interior Q-owner the winner route is exactly
the maximum of the **three** explicit slot contributions `c`, `d`,
`u_* = min(d-1, p-1)` — hence `O(1)` winner pieces. -/
theorem qOwner_field_three {α : Type} [DecidableEq α] (q k : Nat → α)
    {Tq Tk a b c d p : Nat} (h1 : a < p) (h2 : p < b) (t : Nat) :
    field (qOwnerCompressed q k Tq Tk a b c d p) t
      = rmax (qSlot q k Tq Tk a b c d p c t)
          (rmax (qSlot q k Tq Tk a b c d p d t)
                (qSlot q k Tq Tk a b c d p (min (d - 1) (p - 1)) t)) := by
  have hf : field (qOwnerCompressed q k Tq Tk a b c d p) t
      = rmaxList ((QKept q k Tq Tk a b c d p).map (fun b => bval b t)) := by
    unfold qOwnerCompressed field
    rw [List.map_map]
    exact congrArg rmaxList (List.map_congr_left (fun b _ => rfl))
  rw [hf]
  have hsub := qOwner_filter_subset q k Tq Tk a b c d p h1 h2
  have hvalid : Valid (rmaxList ((QKept q k Tq Tk a b c d p).map (fun b => bval b t))) :=
    valid_rmaxList _ (fun r hr => by
      rw [List.mem_map] at hr; obtain ⟨b, _, rfl⟩ := hr; exact bval_valid b t)
  apply rle_antisymm
  · apply rmaxList_lub _ _ (valid_rmax _ _
      (qSlot_valid q k Tq Tk a b c d p c t)
      (valid_rmax _ _ (qSlot_valid q k Tq Tk a b c d p d t)
        (qSlot_valid q k Tq Tk a b c d p (min (d - 1) (p - 1)) t)))
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨x, hx, hrfl⟩ := hr
    rw [← hrfl]
    have h3 := hsub hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h3
    rcases h3 with hA | hB | hC
    · rw [hA]
      have heq : bval (mkBridge q k Tq Tk p c) t = qSlot q k Tq Tk a b c d p c t := by
        unfold qSlot; rw [if_pos (by rw [← hA]; exact hx)]
      rw [heq]
      exact rle_rmax_left _ _
    · rw [hB]
      have heq : bval (mkBridge q k Tq Tk p d) t = qSlot q k Tq Tk a b c d p d t := by
        unfold qSlot; rw [if_pos (by rw [← hB]; exact hx)]
      rw [heq]
      refine rle_trans _ _ _ (rle_rmax_left _ _) (rle_rmax_right _ _)
    · rw [hC]
      have heq : bval (mkBridge q k Tq Tk p (min (d - 1) (p - 1))) t
          = qSlot q k Tq Tk a b c d p (min (d - 1) (p - 1)) t := by
        unfold qSlot; rw [if_pos (by rw [← hC]; exact hx)]
      rw [heq]
      refine rle_trans _ _ _ (rle_rmax_right _ _) (rle_rmax_right _ _)
  · apply (rle_rmax_lub _ _ _).mpr
    refine ⟨?_, (rle_rmax_lub _ _ _).mpr ⟨?_, ?_⟩⟩
    · unfold qSlot
      by_cases hm : mkBridge q k Tq Tk p c ∈ QKept q k Tq Tk a b c d p
      · rw [if_pos hm]; exact rle_rmaxList _ _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
      · rw [if_neg hm]; exact valid_rle_unmatched _ hvalid
    · unfold qSlot
      by_cases hm : mkBridge q k Tq Tk p d ∈ QKept q k Tq Tk a b c d p
      · rw [if_pos hm]; exact rle_rmaxList _ _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
      · rw [if_neg hm]; exact valid_rle_unmatched _ hvalid
    · unfold qSlot
      by_cases hm : mkBridge q k Tq Tk p (min (d - 1) (p - 1)) ∈ QKept q k Tq Tk a b c d p
      · rw [if_pos hm]; exact rle_rmaxList _ _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
      · rw [if_neg hm]; exact valid_rle_unmatched _ hvalid

/-! ### §11.1 (K side): the K-side winner is one of at most three slot contributions -/

/-- A K-edge slot's contribution at `t` (`unmatched` when the slot is not a live
kept centre). -/
def kSlot {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d u : Nat) (p : Nat)
    (t : Nat) : Route :=
  if mkBridge q k Tq Tk p u ∈ KKept q k Tq Tk a b c d u then bval (mkBridge q k Tq Tk p u) t
  else unmatched

theorem kSlot_valid {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d u p t : Nat) :
    Valid (kSlot q k Tq Tk a b c d u p t) := by
  unfold kSlot; split
  · exact bval_valid _ _
  · exact valid_unmatched

theorem kSlot_eq_bval {α : Type} [DecidableEq α] (q k : Nat → α) (Tq Tk a b c d u p : Nat)
    (hx : mkBridge q k Tq Tk p u ∈ KKept q k Tq Tk a b c d u) (t : Nat) :
    kSlot q k Tq Tk a b c d u p t = bval (mkBridge q k Tq Tk p u) t := by
  unfold kSlot; rw [if_pos hx]

/-- The two K-edge slots' `rmax` equals the whole kept-centre field. -/
theorem kEdge_rmax_eq {α : Type} [DecidableEq α] (q k : Nat → α)
    {Tq Tk a b c d u : Nat} (h1 : c < u) (h2 : u < d) (t : Nat) :
    rmaxList ((KKept q k Tq Tk a b c d u).map (fun b => bval b t))
      = rmax (kSlot q k Tq Tk a b c d u a t) (kSlot q k Tq Tk a b c d u b t) := by
  have hsub := kOwner_filter_subset q k Tq Tk a b c d u h1 h2
  have hvalid := valid_rmaxList ((KKept q k Tq Tk a b c d u).map (fun b => bval b t))
    (fun r hr => by rw [List.mem_map] at hr; obtain ⟨b, _, rfl⟩ := hr; exact bval_valid b t)
  apply rle_antisymm
  · apply rmaxList_lub _ _
      (valid_rmax _ _ (kSlot_valid q k Tq Tk a b c d u a t) (kSlot_valid q k Tq Tk a b c d u b t))
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨x, hx, hrfl⟩ := hr
    rw [← hrfl]
    have h3 := hsub hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h3
    rcases h3 with hA | hB
    · rw [hA]
      have heq : bval (mkBridge q k Tq Tk a u) t = kSlot q k Tq Tk a b c d u a t := by
        unfold kSlot; rw [if_pos (by rw [← hA]; exact hx)]
      rw [heq]; exact rle_rmax_left _ _
    · rw [hB]
      have heq : bval (mkBridge q k Tq Tk b u) t = kSlot q k Tq Tk a b c d u b t := by
        unfold kSlot; rw [if_pos (by rw [← hB]; exact hx)]
      rw [heq]; exact rle_rmax_right _ _
  · apply (rle_rmax_lub _ _ _).mpr
    refine ⟨?_, ?_⟩
    · by_cases hm : mkBridge q k Tq Tk a u ∈ KKept q k Tq Tk a b c d u
      · unfold kSlot; rw [if_pos hm]
        exact rle_rmaxList _ _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
      · unfold kSlot; rw [if_neg hm]; exact valid_rle_unmatched _ hvalid
    · by_cases hm : mkBridge q k Tq Tk b u ∈ KKept q k Tq Tk a b c d u
      · unfold kSlot; rw [if_pos hm]
        exact rle_rmaxList _ _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
      · unfold kSlot; rw [if_neg hm]; exact valid_rle_unmatched _ hvalid

/-- **§11.1 (K side).**  For a strict-interior K-owner the winner route is exactly
the maximum of the **three** explicit slots: the interior bulk `kInteriorBulk`
plus the two Q-edge slots `a`, `b` — hence `O(1)` winner pieces. -/
theorem kOwner_field_three {α : Type} [DecidableEq α] (q k : Nat → α)
    {Tq Tk a b c d u : Nat} (h1 : c < u) (h2 : u < d) (t : Nat) :
    field (kOwnerCompressed q k Tq Tk a b c d u) t
      = rmax (bulkRoute a b u t)
          (rmax (kSlot q k Tq Tk a b c d u a t) (kSlot q k Tq Tk a b c d u b t)) := by
  have hf : field (kOwnerCompressed q k Tq Tk a b c d u) t
      = rmax (bulkRoute a b u t)
          (rmaxList ((KKept q k Tq Tk a b c d u).map (fun b => bval b t))) := by
    unfold kOwnerCompressed field KKept kOwnerKeptList
    rw [if_pos ⟨h1, h2⟩]
    simp only [List.map_append, List.map_map, List.singleton_append, List.map_cons, List.map_nil,
      rmaxList]
    rfl
  rw [hf, kEdge_rmax_eq q k h1 h2 t]

end WinnerPieces

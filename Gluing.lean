import Std
import Route
import OwnerCompress
import OwnerCorrect
import WinnerPieces

/-!
## Phase H — step 12a: multi-run *semantic* gluing

Step 11 (both sides) proves each fixed-owner compression exact.  Gluing those
blocks is now pure algebra: the field of a concatenation is the `rmax` of the
blocks' fields (`Route.rmaxList_append`), so the whole multi-run IR is the fold
`rmaxList` of the per-block fields.  No `O(R_K)` claim here (that is 12b).
-/

namespace Gluing
open Route Lcs Repair RosBridge OwnerBridges OwnerCompress OwnerCorrect OwnerCorrectK

/-- The value a candidate contributes at `t` (matching `field`'s map). -/
def cval (c : Cand) (t : Nat) : Route :=
  if c.lo ≤ t ∧ t ≤ c.hi then c.rt t else unmatched

theorem field_eq_map (cs : List Cand) (t : Nat) :
    field cs t = rmaxList (cs.map (fun c => cval c t)) := rfl

theorem fieldBridges_eq_map (bs : List Bridge) (t : Nat) :
    fieldBridges bs t = rmaxList (bs.map (fun b => bval b t)) := rfl

/-! ### The gluing law -/

/-- **Gluing law (candidates).**  The field of a concatenation is the `rmax` of
the fields. -/
theorem field_append (cs₁ cs₂ : List Cand) (t : Nat)
    (hv : ∀ c ∈ cs₂, Valid (cval c t)) :
    field (cs₁ ++ cs₂) t = rmax (field cs₁ t) (field cs₂ t) := by
  unfold field
  rw [List.map_append, rmaxList_append _ _ (fun r hr => by
    rw [List.mem_map] at hr; obtain ⟨c, hc, rfl⟩ := hr; exact hv c hc)]

/-- **Gluing law (bridges).**  No side condition: every `bval` is valid. -/
theorem fieldBridges_append (bs₁ bs₂ : List Bridge) (t : Nat) :
    fieldBridges (bs₁ ++ bs₂) t = rmax (fieldBridges bs₁ t) (fieldBridges bs₂ t) := by
  unfold fieldBridges
  rw [List.map_append, rmaxList_append _ _ (fun r hr => by
    rw [List.mem_map] at hr; obtain ⟨b, _, rfl⟩ := hr; exact bval_valid b t)]

/-- **Gluing law, many blocks** (`flatten` version). -/
theorem field_flatten (blocks : List (List Cand)) (t : Nat)
    (h : ∀ c ∈ blocks.flatten, Valid (cval c t)) :
    field blocks.flatten t = rmaxList (blocks.map (fun b => field b t)) := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatten_cons, field_append b bs.flatten t
        (fun c hc => h c (List.mem_append.mpr (Or.inr hc))),
      ih (fun c hc => h c (List.mem_append.mpr (Or.inr hc)))]
    rfl

theorem fieldBridges_flatten (blocks : List (List Bridge)) (t : Nat) :
    fieldBridges blocks.flatten t = rmaxList (blocks.map (fun b => fieldBridges b t)) := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatten_cons, fieldBridges_append, ih]
    rfl

/-! ### The gluing theorem -/

/-- **step 12a (binary).**  Gluing two compressed blocks that each match their
actual block.  Iterating this (or `glue_flatten`) covers any number of runs. -/
theorem glue_two (cs₁ cs₂ : List Cand) (bs₁ bs₂ : List Bridge) (t : Nat)
    (h₁ : field cs₁ t = fieldBridges bs₁ t) (h₂ : field cs₂ t = fieldBridges bs₂ t)
    (hv : ∀ c ∈ cs₂, Valid (cval c t)) :
    field (cs₁ ++ cs₂) t = fieldBridges (bs₁ ++ bs₂) t := by
  rw [field_append cs₁ cs₂ t hv, fieldBridges_append, h₁, h₂]

/-- **step 12a (many).**  Given a list of `(compressed block, actual block)` pairs
where each compressed block's `field` matches its actual block, the glued
(multi-run) field matches the glued actual field.  This is the multi-run skyline
**semantic** gluing. -/
theorem glue_pairs (pairs : List (List Cand × List Bridge)) (t : Nat)
    (h : ∀ p ∈ pairs, field p.1 t = fieldBridges p.2 t)
    (hv : ∀ p ∈ pairs, ∀ c ∈ p.1, Valid (cval c t)) :
    field (pairs.map (fun p => p.1)).flatten t
      = fieldBridges (pairs.map (fun p => p.2)).flatten t := by
  rw [field_flatten (pairs.map (fun p => p.1)) t (fun c hc => by
        rw [List.mem_flatten] at hc; obtain ⟨b, hb, hcb⟩ := hc
        rw [List.mem_map] at hb; obtain ⟨p, hp, rfl⟩ := hb
        exact hv p hp c hcb),
      fieldBridges_flatten (pairs.map (fun p => p.2)) t]
  congr 1
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left (fun p hp => h p hp)

end Gluing

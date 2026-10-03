import Std
import Route
import Repair
import RosBridge

/-!
## Phase H (new) — step 9: fixed-owner bridge collections

`qOwnerBridges` / `kOwnerBridges` enumerate the *actual* repair bridges of a
one-bit run pair `([a,b],[c,d])` for a fixed owner, with the owner / bit /
run-pair conditions made explicit.

Note on the **bit** condition: the bridge algebra below never uses the bit label
`j` — `Run-Rectangle` (`run_rectangle_*`) and `Boundary-Support`
(`repair_*_boundary_support`) only need the two run symbols to be **different**
(`αs ≠ βs`), which is exactly "one-bit adjacent".  `j` is therefore carried as a
bookkeeping label on the run pair, not on each bridge.
-/

namespace OwnerBridges
open Route Lcs Repair RosBridge

variable {α : Type} [DecidableEq α]

/-- The bridge attached to a position pair `(p,u)`. -/
def mkBridge (q k : Nat → α) (Tq Tk p u : Nat) : Bridge :=
  ⟨p, u, leftCtx q k p u, rightCtx q k Tq Tk p u⟩

@[simp] theorem mkBridge_p (q k : Nat → α) (Tq Tk p u : Nat) :
    (mkBridge q k Tq Tk p u).p = p := rfl

@[simp] theorem mkBridge_u (q k : Nat → α) (Tq Tk p u : Nat) :
    (mkBridge q k Tq Tk p u).u = u := rfl

/-- Positional condition of a causal centre inside the run rectangle `[a,b]×[c,d]`. -/
def Centre (a b c d p u : Nat) : Prop := a ≤ p ∧ p ≤ b ∧ c ≤ u ∧ u ≤ d ∧ u < p

/-- **Q-owner collection**: all causal K-centres `u` for the fixed Q-owner `p`
(empty unless `p ∈ [a,b]`). -/
def qOwnerBridges (q k : Nat → α) (Tq Tk a b c d p : Nat) : List Bridge :=
  if a ≤ p ∧ p ≤ b then
    ((List.range (d + 1)).filter (fun u => decide (c ≤ u ∧ u ≤ d ∧ u < p))).map
      (fun u => mkBridge q k Tq Tk p u)
  else []

/-- **K-owner collection**: all causal Q-centres `p` for the fixed K-owner `u`
(empty unless `u ∈ [c,d]`). -/
def kOwnerBridges (q k : Nat → α) (Tq Tk a b c d u : Nat) : List Bridge :=
  if c ≤ u ∧ u ≤ d then
    ((List.range (b + 1)).filter (fun p => decide (a ≤ p ∧ p ≤ b ∧ u < p))).map
      (fun p => mkBridge q k Tq Tk p u)
  else []

theorem mem_qOwnerBridges {q k : Nat → α} {Tq Tk a b c d p : Nat} {x : Bridge} :
    x ∈ qOwnerBridges q k Tq Tk a b c d p ↔
      a ≤ p ∧ p ≤ b ∧ ∃ u, c ≤ u ∧ u ≤ d ∧ u < p ∧ x = mkBridge q k Tq Tk p u := by
  unfold qOwnerBridges
  by_cases h : a ≤ p ∧ p ≤ b
  · rw [if_pos h, List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [List.mem_filter] at hu
      obtain ⟨hr, hd⟩ := hu
      rw [List.mem_range] at hr
      simp only [decide_eq_true_eq] at hd
      exact ⟨h.1, h.2, u, hd.1, hd.2.1, hd.2.2, rfl⟩
    · rintro ⟨_, _, u, h1, h2, h3, rfl⟩
      refine ⟨u, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨by rw [List.mem_range]; omega, by simp [h1, h2, h3]⟩
  · rw [if_neg h]
    constructor
    · intro hx; simp at hx
    · rintro ⟨h1, h2, _⟩; exact absurd ⟨h1, h2⟩ h

theorem mem_kOwnerBridges {q k : Nat → α} {Tq Tk a b c d u : Nat} {x : Bridge} :
    x ∈ kOwnerBridges q k Tq Tk a b c d u ↔
      c ≤ u ∧ u ≤ d ∧ ∃ p, a ≤ p ∧ p ≤ b ∧ u < p ∧ x = mkBridge q k Tq Tk p u := by
  unfold kOwnerBridges
  by_cases h : c ≤ u ∧ u ≤ d
  · rw [if_pos h, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [List.mem_filter] at hp
      obtain ⟨hr, hd⟩ := hp
      rw [List.mem_range] at hr
      simp only [decide_eq_true_eq] at hd
      exact ⟨h.1, h.2, p, hd.1, hd.2.1, hd.2.2, rfl⟩
    · rintro ⟨_, _, p, h1, h2, h3, rfl⟩
      refine ⟨p, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨by rw [List.mem_range]; omega, by simp [h1, h2, h3]⟩
  · rw [if_neg h]
    constructor
    · intro hx; simp at hx
    · rintro ⟨h1, h2, _⟩; exact absurd ⟨h1, h2⟩ h

/-- **Common birth**: every `qOwnerBridges` element is born at the fixed owner `p`
(this is what lets step 10 use `CommonBirth.common_birth_winner_iff`). -/
theorem qOwnerBridges_birth {q k : Nat → α} {Tq Tk a b c d p : Nat} {x : Bridge}
    (h : x ∈ qOwnerBridges q k Tq Tk a b c d p) : x.p = p := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_qOwnerBridges.mp h
  rfl

/-- Every `kOwnerBridges` element has K-centre the fixed owner `u`. -/
theorem kOwnerBridges_u {q k : Nat → α} {Tq Tk a b c d u : Nat} {x : Bridge}
    (h : x ∈ kOwnerBridges q k Tq Tk a b c d u) : x.u = u := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_kOwnerBridges.mp h
  rfl

/-- A fixed-owner, fixed-bit repair query over one one-bit run pair. -/
structure Query where
  /-- Q-run `[a,b]`. -/
  a : Nat
  b : Nat
  /-- K-run `[c,d]`. -/
  c : Nat
  d : Nat
  /-- The flipped bit label `j` (bookkeeping; the algebra only needs `αs ≠ βs`). -/
  bit : Nat
  /-- `true` = Q-owner (`p` fixed), `false` = K-owner (`u` fixed). -/
  isQ : Bool
  /-- The fixed owner position. -/
  owner : Nat

/-- **The actual bridges of a query** (owner / side / run-pair resolved). -/
def Query.bridges (Q : Query) (q k : Nat → α) (Tq Tk : Nat) : List Bridge :=
  match Q.isQ with
  | true => qOwnerBridges q k Tq Tk Q.a Q.b Q.c Q.d Q.owner
  | false => kOwnerBridges q k Tq Tk Q.a Q.b Q.c Q.d Q.owner

theorem mem_Query_bridges {Q : Query} {q k : Nat → α} {Tq Tk : Nat} {x : Bridge} :
    x ∈ Q.bridges q k Tq Tk ↔
      (Q.isQ = true ∧
        Q.a ≤ Q.owner ∧ Q.owner ≤ Q.b ∧
        ∃ u, Q.c ≤ u ∧ u ≤ Q.d ∧ u < Q.owner ∧ x = mkBridge q k Tq Tk Q.owner u) ∨
      (Q.isQ = false ∧
        Q.c ≤ Q.owner ∧ Q.owner ≤ Q.d ∧
        ∃ p, Q.a ≤ p ∧ p ≤ Q.b ∧ Q.owner < p ∧ x = mkBridge q k Tq Tk p Q.owner) := by
  cases hq : Q.isQ
  · simp only [Query.bridges, hq, mem_kOwnerBridges]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact Or.inr ⟨trivial, h1, h2, h3⟩
    · rintro (⟨ht, _⟩ | ⟨_, h1, h2, h3⟩)
      · exact absurd ht (by simp [hq])
      · exact ⟨h1, h2, h3⟩
  · simp only [Query.bridges, hq, mem_qOwnerBridges]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact Or.inl ⟨trivial, h1, h2, h3⟩
    · rintro (⟨_, h1, h2, h3⟩ | ⟨hf, _⟩)
      · exact ⟨h1, h2, h3⟩
      · exact absurd hf (by simp [hq])

end OwnerBridges

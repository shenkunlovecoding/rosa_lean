import Std
import Repair
import RunRectangleLcp

/-!
## Phase G core — repair four-edge coverage and degenerate overlap

For a run-rectangle `[a,b] × [c,d]`, with horizontal coordinate `p` and vertical
coordinate `u`, this file fixes the following exact boundary predicates:

* left edge:   `p = a`
* right edge:  `p = b`
* bottom edge: `u = c`
* top edge:    `u = d`

The strict interior is `a < p < b ∧ c < u < d`.

The definition-independent core below proves that every point of the rectangle
is either strict-interior or on one of these four edges, and that at most four
distinct edge labels can hold.  The repair-specific bridge to `Repair.leftCtx`
and `Repair.rightCtx` then proves that a positive left/right context forces one
of the four edges.  Finally, singleton run widths/heights and corners are made
explicit: edge membership is intentionally not a partition into disjoint
classes, since degenerate run length 1 makes several named edges coincide.

### Wider Phase G closure

This file isolates the semantic coverage/overlap core.  The remaining string-level
certificate and range-count assembly is supplied by `BoundaryCertificates`,
`BoundaryZeroCertificates`, `BoundaryRangeCount`, `BoundaryRecursive`,
`BoundaryRunExtractor`, and `BoundaryOptionalWindow`.
-/

open Lcs RunRect Repair

set_option linter.unusedSectionVars false

namespace BoundaryPartition

variable {α : Type} [DecidableEq α]

/-- Exact left-edge predicate inside a run rectangle. -/
abbrev OnLeft (a p : Nat) : Prop := p = a

/-- Exact right-edge predicate inside a run rectangle. -/
abbrev OnRight (b p : Nat) : Prop := p = b

/-- Exact bottom-edge predicate inside a run rectangle. -/
abbrev OnBottom (c u : Nat) : Prop := u = c

/-- Exact top-edge predicate inside a run rectangle. -/
abbrev OnTop (d u : Nat) : Prop := u = d

/-- Union of the four named boundary edges. -/
def OnEdge (a b c d p u : Nat) : Prop :=
  OnLeft a p ∨ OnRight b p ∨ OnBottom c u ∨ OnTop d u

/-- Strict two-dimensional interior of the run rectangle. -/
def StrictInterior (a b c d p u : Nat) : Prop :=
  a < p ∧ p < b ∧ c < u ∧ u < d

/-- Membership of a centre in the closed run rectangle. -/
def RectPoint (a b c d p u : Nat) : Prop :=
  a ≤ p ∧ p ≤ b ∧ c ≤ u ∧ u ≤ d

/-- Strict interior points are disjoint from the four-edge union. -/
theorem strictInterior_not_onEdge {a b c d p u : Nat}
    (hI : StrictInterior a b c d p u) : ¬ OnEdge a b c d p u := by
  rcases hI with ⟨hap, hpb, hcu, hud⟩
  intro hE
  rcases hE with hleft | hright | hbottom | htop
  · dsimp [OnLeft] at hleft
    omega
  · dsimp [OnRight] at hright
    omega
  · dsimp [OnBottom] at hbottom
    omega
  · dsimp [OnTop] at htop
    omega

/-- For a point of the closed rectangle, being on an edge is exactly the
complement of being in the strict interior. -/
theorem onEdge_iff_not_strictInterior {a b c d p u : Nat}
    (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d) :
    OnEdge a b c d p u ↔ ¬ StrictInterior a b c d p u := by
  constructor
  · intro hE hI
    exact strictInterior_not_onEdge hI hE
  · intro hnot
    by_cases hpa : p = a
    · exact Or.inl hpa
    by_cases hpb' : p = b
    · exact Or.inr (Or.inl hpb')
    by_cases huc : u = c
    · exact Or.inr (Or.inr (Or.inl huc))
    by_cases hud' : u = d
    · exact Or.inr (Or.inr (Or.inr hud'))
    · exfalso
      apply hnot
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- Covering form: every point of the closed rectangle is strict-interior or on
one of the four named edges. -/
theorem rectPoint_strictInterior_or_onEdge {a b c d p u : Nat}
    (h : RectPoint a b c d p u) :
    StrictInterior a b c d p u ∨ OnEdge a b c d p u := by
  rcases h with ⟨hp, hpb, hu, hud⟩
  by_cases hI : StrictInterior a b c d p u
  · exact Or.inl hI
  · exact Or.inr ((onEdge_iff_not_strictInterior hp hpb hu hud).2 hI)

/-- A mismatched run rectangle has both guarded contexts zero at every strict
interior centre. -/
theorem strictInterior_contexts_zero
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs) {p u : Nat}
    (hI : StrictInterior a b c d p u) :
    leftCtx q k p u = 0 ∧ rightCtx q k Tq Tk p u = 0 := by
  rcases hI with ⟨hap, hpb, hcu, hud⟩
  have hp0 : 0 < p := by omega
  have hu0 : 0 < u := by omega
  have hraw :=
    repair_strict_interior_trivial (q := q) (k := k) (Tq := Tq) (Tk := Tk)
      (a := a) (b := b) (c := c) (d := d) (αs := αs) (βs := βs)
      hQ hK hne hap hpb hcu hud
  constructor
  · rw [leftCtx_eq (q := q) (k := k) hp0 hu0]
    exact hraw.1
  · simpa [rightCtx] using hraw.2

/-- If either guarded repair context is positive, the centre lies on one of the
four named edges.  This is the repair-specific four-edge coverage theorem. -/
theorem positive_context_edge_cover
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d)
    (hpos : 0 < leftCtx q k p u ∨ 0 < rightCtx q k Tq Tk p u) :
    OnEdge a b c d p u := by
  rcases hpos with hL | hR
  · have hp0 : 0 < p := by
      apply Nat.pos_of_ne_zero
      intro hpz
      have hz : leftCtx q k p u = 0 := leftCtx_zero (q := q) (k := k) (Or.inl hpz)
      omega
    have hu0 : 0 < u := by
      apply Nat.pos_of_ne_zero
      intro huz
      have hz : leftCtx q k p u = 0 := leftCtx_zero (q := q) (k := k) (Or.inr huz)
      omega
    have hraw : 0 < lcsLen q k (p - 1) (u - 1) := by
      have hL' := hL
      rw [leftCtx_eq (q := q) (k := k) hp0 hu0] at hL'
      exact hL'
    rcases repair_left_boundary_support hQ hK hne hp hpb hu hud hraw with hpa | huc
    · exact Or.inl hpa
    · exact Or.inr (Or.inr (Or.inl huc))
  · have hraw : 0 < lcpLen q k Tq Tk p u := by
      simpa [rightCtx] using hR
    rcases repair_right_boundary_support hQ hK hne hp hpb hu hud hraw with hpb' | hud'
    · exact Or.inr (Or.inl hpb')
    · exact Or.inr (Or.inr (Or.inr hud'))


/-- Total dichotomy for a centre of a mismatched closed rectangle: either it is
on one of the four named edges, or it is strict-interior and both guarded
contexts are zero. -/
theorem context_edge_cover_or_strictInterior_zero
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (hne : αs ≠ βs)
    {p u : Nat} (hp : a ≤ p) (hpb : p ≤ b) (hu : c ≤ u) (hud : u ≤ d) :
    OnEdge a b c d p u ∨
      (leftCtx q k p u = 0 ∧ rightCtx q k Tq Tk p u = 0) := by
  by_cases hI : StrictInterior a b c d p u
  · exact Or.inr (strictInterior_contexts_zero hQ hK hne hI)
  · exact Or.inl ((onEdge_iff_not_strictInterior hp hpb hu hud).2 hI)

/-! ### Definition-independent edge membership and overlap -/

/-- The four edge labels, in a fixed order. -/
inductive EdgeKind where
  | left
  | right
  | bottom
  | top
  deriving DecidableEq, Repr

/-- The full ordered edge-label list. -/
def edgeKinds : List EdgeKind := [.left, .right, .bottom, .top]


/-- The canonical edge-label list has no duplicates. -/
theorem edgeKinds_nodup : edgeKinds.Nodup := by
  decide

/-- Interpretation of an edge label as the corresponding boundary predicate. -/
def EdgeKind.holds (a b c d p u : Nat) : EdgeKind → Prop
  | .left => OnLeft a p
  | .right => OnRight b p
  | .bottom => OnBottom c u
  | .top => OnTop d u

instance (a b c d p u : Nat) : DecidablePred (EdgeKind.holds a b c d p u) := by
  intro e
  cases e <;> dsimp [EdgeKind.holds, OnLeft, OnRight, OnBottom, OnTop] <;> infer_instance

/-- Ordered list of all edge labels that currently hold.  The underlying label
list has no duplicates, so its length is the number of distinct memberships. -/
def edgeMemberships (a b c d p u : Nat) : List EdgeKind :=
  edgeKinds.filter (fun e => decide (EdgeKind.holds a b c d p u e))


/-- Filtering the duplicate-free label list preserves duplicate-freedom. -/
theorem edgeMemberships_nodup (a b c d p u : Nat) :
    (edgeMemberships a b c d p u).Nodup := by
  unfold edgeMemberships
  exact List.Nodup.sublist List.filter_sublist edgeKinds_nodup

/-- Number of distinct edge memberships. -/
def edgeMembershipCount (a b c d p u : Nat) : Nat :=
  (edgeMemberships a b c d p u).length

theorem mem_edgeMemberships_iff (a b c d p u : Nat) (e : EdgeKind) :
    e ∈ edgeMemberships a b c d p u ↔ EdgeKind.holds a b c d p u e := by
  cases e <;> simp [edgeMemberships, edgeKinds, EdgeKind.holds]
  all_goals
    exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

/-- The exact universal upper bound on edge overlap. -/
theorem edgeMembershipCount_le_four (a b c d p u : Nat) :
    edgeMembershipCount a b c d p u ≤ 4 := by
  unfold edgeMembershipCount edgeMemberships edgeKinds
  exact Nat.le_trans (List.length_filter_le _ _) (by decide)

theorem edgeMemberships_length_le_four (a b c d p u : Nat) :
    (edgeMemberships a b c d p u).length ≤ 4 :=
  edgeMembershipCount_le_four a b c d p u

/-- The four-predicate union is exactly membership in the ordered edge list. -/
theorem onEdge_iff_exists_mem_edgeMemberships (a b c d p u : Nat) :
    OnEdge a b c d p u ↔ ∃ e, e ∈ edgeMemberships a b c d p u := by
  constructor
  · intro h
    rcases h with hleft | hright | hbottom | htop
    · refine ⟨EdgeKind.left, ?_⟩
      rw [mem_edgeMemberships_iff]
      exact hleft
    · refine ⟨EdgeKind.right, ?_⟩
      rw [mem_edgeMemberships_iff]
      exact hright
    · refine ⟨EdgeKind.bottom, ?_⟩
      rw [mem_edgeMemberships_iff]
      exact hbottom
    · refine ⟨EdgeKind.top, ?_⟩
      rw [mem_edgeMemberships_iff]
      exact htop
  · rintro ⟨e, he⟩
    have hh := (mem_edgeMemberships_iff a b c d p u e).1 he
    cases e with
    | left => exact Or.inl (by simpa [EdgeKind.holds] using hh)
    | right => exact Or.inr (Or.inl (by simpa [EdgeKind.holds] using hh))
    | bottom => exact Or.inr (Or.inr (Or.inl (by simpa [EdgeKind.holds] using hh)))
    | top => exact Or.inr (Or.inr (Or.inr (by simpa [EdgeKind.holds] using hh)))

/-! ### Degenerate overlaps and corners -/

theorem left_right_overlap_of_width_one {a b p : Nat}
    (hab : a = b) (hp : OnLeft a p) : OnLeft a p ∧ OnRight b p := by
  constructor
  · exact hp
  · dsimp [OnRight]
    omega

theorem bottom_top_overlap_of_height_one {c d u : Nat}
    (hcd : c = d) (hu : OnBottom c u) : OnBottom c u ∧ OnTop d u := by
  constructor
  · exact hu
  · dsimp [OnTop]
    omega

/-- A singleton rectangle catches all four labels (the degenerate four-edge
overlap used to handle run length 1). -/
theorem all_four_edges_of_singleton {a b c d p u : Nat}
    (hab : a = b) (hcd : c = d) (hp : p = a) (hu : u = c) :
    OnLeft a p ∧ OnRight b p ∧ OnBottom c u ∧ OnTop d u := by
  constructor
  · exact hp
  constructor
  · dsimp [OnRight]
    omega
  constructor
  · exact hu
  · dsimp [OnTop]
    omega

/-- In a singleton rectangle the membership list is the full four-edge list. -/
theorem edgeMemberships_of_singleton {a b c d p u : Nat}
    (hab : a = b) (hcd : c = d) (hp : p = a) (hu : u = c) :
    edgeMemberships a b c d p u = edgeKinds := by
  simp [edgeMemberships, edgeKinds, EdgeKind.holds, OnLeft, OnRight, OnBottom, OnTop,
    hab, hcd, hp, hu]

/-- A singleton rectangle has exactly four distinct edge memberships. -/
theorem edgeMembershipCount_of_singleton {a b c d p u : Nat}
    (hab : a = b) (hcd : c = d) (hp : p = a) (hu : u = c) :
    edgeMembershipCount a b c d p u = 4 := by
  unfold edgeMembershipCount
  rw [edgeMemberships_of_singleton hab hcd hp hu]
  simp [edgeKinds]

/-- A width-one run makes left and right coincide throughout its height. -/
theorem edgeMemberships_of_width_one {a b c d p u : Nat}
    (hab : a = b) (hp : p = a) (hcu : c < u) (hud : u < d) :
    edgeMemberships a b c d p u = [EdgeKind.left, EdgeKind.right] := by
  have huc : ¬ u = c := by omega
  have hud' : ¬ u = d := by omega
  simp [edgeMemberships, edgeKinds, EdgeKind.holds, OnLeft, OnRight, OnBottom, OnTop,
    hab, hp, huc, hud']

/-- A height-one run makes bottom and top coincide throughout its width. -/
theorem edgeMemberships_of_height_one {a b c d p u : Nat}
    (hcd : c = d) (hu : u = c) (hap : a < p) (hpb : p < b) :
    edgeMemberships a b c d p u = [EdgeKind.bottom, EdgeKind.top] := by
  have hpa : ¬ p = a := by omega
  have hpb' : ¬ p = b := by omega
  simp [edgeMemberships, edgeKinds, EdgeKind.holds, OnLeft, OnRight, OnBottom, OnTop,
    hcd, hu, hpa, hpb']

/-- Bottom-left corner of a non-degenerate rectangle has exactly the two labels
`left` and `bottom`. -/
theorem edgeMemberships_bottom_left_corner {a b c d : Nat}
    (hab : a < b) (hcd : c < d) :
    edgeMemberships a b c d a c = [EdgeKind.left, EdgeKind.bottom] := by
  have hba : ¬ a = b := by omega
  have hdc : ¬ c = d := by omega
  simp [edgeMemberships, edgeKinds, EdgeKind.holds, OnLeft, OnRight, OnBottom, OnTop,
    hba, hdc]

/-- Bottom-right corner of a non-degenerate rectangle has exactly the two labels
`right` and `bottom`. -/
theorem edgeMemberships_bottom_right_corner {a b c d : Nat}
    (hab : a < b) (hcd : c < d) :
    edgeMemberships a b c d b c = [EdgeKind.right, EdgeKind.bottom] := by
  have hab' : ¬ b = a := by omega
  have hdc : ¬ c = d := by omega
  simp [edgeMemberships, edgeKinds, EdgeKind.holds, OnLeft, OnRight, OnBottom, OnTop,
    hab', hdc]

/-- Top-left corner of a non-degenerate rectangle has exactly the two labels
`left` and `top`. -/
theorem edgeMemberships_top_left_corner {a b c d : Nat}
    (hab : a < b) (hcd : c < d) :
    edgeMemberships a b c d a d = [EdgeKind.left, EdgeKind.top] := by
  have hba : ¬ a = b := by omega
  have hcd' : ¬ d = c := by omega
  simp [edgeMemberships, edgeKinds, EdgeKind.holds, OnLeft, OnRight, OnBottom, OnTop,
    hba, hcd']

/-- Top-right corner of a non-degenerate rectangle has exactly the two labels
`right` and `top`. -/
theorem edgeMemberships_top_right_corner {a b c d : Nat}
    (hab : a < b) (hcd : c < d) :
    edgeMemberships a b c d b d = [EdgeKind.right, EdgeKind.top] := by
  have hab' : ¬ b = a := by omega
  have hcd' : ¬ d = c := by omega
  simp [edgeMemberships, edgeKinds, EdgeKind.holds, OnLeft, OnRight, OnBottom, OnTop,
    hab', hcd']

end BoundaryPartition

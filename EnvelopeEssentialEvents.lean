import AffineLifetime

/-!
## Essential-event deduplication and quadratic counting

`AffineLifetime.criticalEvents` is deliberately redundant: it contains every
candidate lifetime event and every ordered-pair crossing window.  This file
turns that coverage list into an ordered duplicate-free event list and proves:

* every raw critical event is retained;
* every winner change forces membership in the essential list;
* the essential list has at most `2n + n(n-1)` entries, i.e.
  `2n + 2 * choose n 2`;
* the existing event-scan correctness theorem is valid verbatim when its
  event side condition is stated over the essential list.

Only integer-time windows are used.
-/

namespace AffineLifetime

open AffEnv

/-! ### Ordered duplicate removal -/

/-- Remove duplicates and keep the order of the surviving last occurrences.
For example, `[a,b,a]` becomes `[b,a]`. -/
def orderedUnique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as =>
      let rest := orderedUnique as
      if a ∈ rest then rest else a :: rest

theorem mem_orderedUnique {α : Type} [DecidableEq α] (a : α) (l : List α) :
    a ∈ orderedUnique l ↔ a ∈ l := by
  induction l generalizing a with
  | nil => simp [orderedUnique]
  | cons x xs ih =>
    dsimp [orderedUnique]
    by_cases hx : x ∈ orderedUnique xs
    · rw [if_pos hx]
      constructor
      · intro ha
        exact List.mem_cons.mpr (Or.inr ((ih a).mp ha))
      · intro h
        rcases List.mem_cons.mp h with hax | ha
        · subst a
          exact hx
        · exact (ih a).mpr ha
    · rw [if_neg hx]
      constructor
      · intro h
        rcases List.mem_cons.mp h with hax | ha
        · subst a
          exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons.mpr (Or.inr ((ih a).mp ha))
      · intro h
        rcases List.mem_cons.mp h with hax | ha
        · subst a
          exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons.mpr (Or.inr ((ih a).mpr ha))

theorem nodup_orderedUnique {α : Type} [DecidableEq α] (l : List α) :
    (orderedUnique l).Nodup := by
  induction l with
  | nil => simp [orderedUnique]
  | cons x xs ih =>
    dsimp [orderedUnique]
    by_cases hx : x ∈ orderedUnique xs
    · rw [if_pos hx]
      exact ih
    · rw [if_neg hx, List.nodup_cons]
      exact ⟨hx, ih⟩

theorem length_orderedUnique_le {α : Type} [DecidableEq α] (l : List α) :
    (orderedUnique l).length ≤ l.length := by
  induction l with
  | nil => simp [orderedUnique]
  | cons x xs ih =>
    dsimp [orderedUnique]
    by_cases hx : x ∈ orderedUnique xs
    · rw [if_pos hx]
      exact Nat.le_trans ih (Nat.le_succ xs.length)
    · rw [if_neg hx]
      simp only [List.length_cons]
      omega

/-! ### Pair-window symmetry -/

private def pairCriticalCore (A B C D : Int) : List Int :=
  if 0 < A then
    posRootWindow A B
  else if A < 0 then
    negRootWindow A B
  else if B = 0 then
    if 0 < C then
      posRootWindow C D
    else if C < 0 then
      negRootWindow C D
    else
      []
  else
    []

private theorem negRootWindow_neg_neg (A B : Int) :
    negRootWindow (-A) (-B) = posRootWindow A B := by
  unfold negRootWindow
  rw [Int.neg_neg, Int.neg_neg]

private theorem pairCriticalCore_comm (A B C D : Int) :
    pairCriticalCore A B C D = pairCriticalCore (-A) (-B) (-C) (-D) := by
  unfold pairCriticalCore
  by_cases hA : 0 < A
  · have hApos' : ¬ 0 < -A := by omega
    have hAneg' : -A < 0 := by omega
    rw [if_pos hA, if_neg hApos', if_pos hAneg']
    exact (negRootWindow_neg_neg A B).symm
  · by_cases hAn : A < 0
    · have hApos' : 0 < -A := by omega
      rw [if_neg hA, if_pos hAn, if_pos hApos']
      simpa using negRootWindow_neg_neg (-A) (-B)
    · have hAz : A = 0 := by omega
      rw [hAz]
      by_cases hB : B = 0
      · rw [hB]
        by_cases hC : 0 < C
        · have hCpos' : ¬ 0 < -C := by omega
          have hCneg' : -C < 0 := by omega
          rw [if_pos hC, if_neg hCpos', if_pos hCneg']
          exact (negRootWindow_neg_neg C D).symm
        · by_cases hCn : C < 0
          · have hCpos' : 0 < -C := by omega
            rw [if_neg hC, if_pos hCn, if_pos hCpos']
            simpa using negRootWindow_neg_neg (-C) (-D)
          · have hCz : C = 0 := by omega
            simp [hCz]
      · have hBpos' : ¬ -B = 0 := by omega
        simp [hB, hBpos']

/-- The two-point pair window is invariant under swapping the ordered pair. -/
theorem pairCritical_comm (a b : Candidate) :
    pairCritical a b = pairCritical b a := by
  have h := pairCriticalCore_comm
    (a.route.aL - b.route.aL) (a.route.bL - b.route.bL)
    (a.route.aE - b.route.aE) (a.route.bE - b.route.bE)
  simpa [pairCritical, pairCriticalCore, Int.neg_sub] using h

theorem pairCritical_self (a : Candidate) : pairCritical a a = [] := by
  dsimp [pairCritical, posRootWindow, negRootWindow]
  simp

/-- Every per-pair crossing window contains at most two integer times. -/
theorem pairCritical_length_le_two (a b : Candidate) :
    (pairCritical a b).length ≤ 2 := by
  dsimp [pairCritical, posRootWindow, negRootWindow]
  split <;> try split <;> try split <;> try split <;> try split
  all_goals simp

/-! ### One canonical window per unordered pair -/

/-- All pairs from distinct positions, oriented by list order:
for the head, pair it with every later element, then recurse on the tail. -/
def unorderedPairs {α : Type} : List α → List (α × α)
  | [] => []
  | a :: as => as.map (fun b => (a, b)) ++ unorderedPairs as

/-- Any two distinct elements occur in `unorderedPairs`, in one of the two
orientations. -/
theorem mem_unorderedPairs_or_swap {α : Type} {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (a, b) ∈ unorderedPairs l ∨ (b, a) ∈ unorderedPairs l := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact (hne rfl).elim
      · left
        simp only [unorderedPairs, List.mem_append, List.mem_map]
        left
        exact ⟨b, hb, rfl⟩
    · rcases hb with rfl | hb
      · right
        simp only [unorderedPairs, List.mem_append, List.mem_map]
        left
        exact ⟨a, ha, rfl⟩
      · rcases ih ha hb with h | h
        · left
          simp only [unorderedPairs, List.mem_append]
          exact Or.inr h
        · right
          simp only [unorderedPairs, List.mem_append]
          exact Or.inr h

/-- Double-counting form of `#unorderedPairs ≤ n(n-1)/2`. -/
theorem two_mul_unorderedPairs_length_le {α : Type} (l : List α) :
    2 * (unorderedPairs l).length ≤ l.length * (l.length - 1) := by
  induction l with
  | nil => simp [unorderedPairs]
  | cons a as ih =>
    rw [unorderedPairs, List.length_append, List.length_map, List.length_cons]
    rw [Nat.mul_add]
    have hm : as.length + 1 - 1 = as.length := Nat.add_sub_cancel as.length 1
    rw [hm, Nat.add_mul, Nat.one_mul]
    by_cases hm0 : as.length = 0
    · have ih' : 2 * (unorderedPairs as).length ≤ 0 := by simpa [hm0] using ih
      have hu : (unorderedPairs as).length = 0 := by omega
      rw [hm0, hu]
      simp
    · have hmpos : 1 ≤ as.length := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hm0)
      have hsub : as.length * (as.length - 1) =
          as.length * as.length - as.length := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have hle : as.length ≤ as.length * as.length :=
        Nat.le_mul_of_pos_left as.length (by omega)
      omega

/-- The raw candidate-event block, kept separate for its exact length. -/
def candidateEventList (cs : List Candidate) : List Int :=
  cs.flatMap candidateEvents

/-- Pair windows with each unordered pair of candidate positions represented
exactly once. -/
def canonicalPairEvents (cs : List Candidate) : List Int :=
  (unorderedPairs cs).flatMap (fun p => pairCritical p.1 p.2)

/-- A non-deduplicated certificate list containing every raw critical event. -/
def canonicalCriticalEvents (cs : List Candidate) : List Int :=
  candidateEventList cs ++ canonicalPairEvents cs

/-- The scan-facing critical-event list, with all duplicate times removed while
preserving first-occurrence order. -/
def essentialEvents (cs : List Candidate) : List Int :=
  orderedUnique (criticalEvents cs)

/-! ### Coverage and exact counting -/

theorem candidateEventList_length (cs : List Candidate) :
    (candidateEventList cs).length = 2 * cs.length := by
  induction cs with
  | nil => simp [candidateEventList]
  | cons c cs ih =>
    rw [candidateEventList, List.flatMap_cons, List.length_append,
      List.length_cons]
    change (candidateEvents c).length + (candidateEventList cs).length =
      2 * (cs.length + 1)
    rw [ih]
    simp [candidateEvents]
    omega

/-- At most two event times per unordered pair, hence at most `n(n-1)` times. -/
theorem canonicalPairEvents_length_le (cs : List Candidate) :
    (canonicalPairEvents cs).length ≤ cs.length * (cs.length - 1) := by
  unfold canonicalPairEvents
  have htwo : ((unorderedPairs cs).flatMap
      (fun p : Candidate × Candidate => pairCritical p.1 p.2)).length ≤
      2 * (unorderedPairs cs).length := by
    induction unorderedPairs cs with
    | nil => simp
    | cons p ps ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have hp : (pairCritical p.1 p.2).length ≤ 2 :=
        pairCritical_length_le_two p.1 p.2
      omega
  have hcount := two_mul_unorderedPairs_length_le cs
  omega

theorem canonicalCriticalEvents_length_le (cs : List Candidate) :
    (canonicalCriticalEvents cs).length ≤
      2 * cs.length + cs.length * (cs.length - 1) := by
  rw [canonicalCriticalEvents, List.length_append]
  have hc := candidateEventList_length cs
  have hp := canonicalPairEvents_length_le cs
  omega

/-- Every raw pair event is represented in the one-canonical-window list. -/
theorem pairEvents_subset_canonicalPairEvents (cs : List Candidate) :
    ∀ q ∈ pairEvents cs, q ∈ canonicalPairEvents cs := by
  intro q hq
  rw [pairEvents, List.mem_flatMap] at hq
  obtain ⟨a, ha, hq⟩ := hq
  rw [List.mem_flatMap] at hq
  obtain ⟨b, hb, hq⟩ := hq
  by_cases hab : a = b
  · subst b
    simp [pairCritical_self] at hq
  · rcases mem_unorderedPairs_or_swap ha hb hab with hp | hp
    · rw [canonicalPairEvents, List.mem_flatMap]
      exact ⟨(a, b), hp, hq⟩
    · rw [canonicalPairEvents, List.mem_flatMap]
      exact ⟨(b, a), hp, by simpa [pairCritical_comm a b] using hq⟩

/-- The canonical certificate retains every raw critical event. -/
theorem criticalEvents_subset_canonicalCriticalEvents (cs : List Candidate) :
    ∀ q ∈ criticalEvents cs, q ∈ canonicalCriticalEvents cs := by
  intro q hq
  rw [criticalEvents, List.mem_append] at hq
  rw [canonicalCriticalEvents, List.mem_append]
  rcases hq with hq | hq
  · left
    simpa [candidateEventList] using hq
  · right
    exact pairEvents_subset_canonicalPairEvents cs q hq

theorem essentialEvents_nodup (cs : List Candidate) :
    (essentialEvents cs).Nodup := by
  unfold essentialEvents
  exact nodup_orderedUnique (criticalEvents cs)

@[simp] theorem mem_essentialEvents {cs : List Candidate} {q : Int} :
    q ∈ essentialEvents cs ↔ q ∈ criticalEvents cs := by
  unfold essentialEvents
  exact mem_orderedUnique q (criticalEvents cs)

theorem criticalEvents_subset_essentialEvents (cs : List Candidate) :
    ∀ q ∈ criticalEvents cs, q ∈ essentialEvents cs := by
  intro q hq
  exact mem_essentialEvents.mpr hq

/-- Explicit quadratic bound.  Since `n(n-1) = 2*C(n,2)`, this is exactly
`2n + 2*C(n,2)` for `n = cs.length`. -/
theorem essentialEvents_length_le (cs : List Candidate) :
    (essentialEvents cs).length ≤
      2 * cs.length + cs.length * (cs.length - 1) := by
  unfold essentialEvents
  have hsub : ∀ q ∈ orderedUnique (criticalEvents cs),
      q ∈ canonicalCriticalEvents cs := by
    intro q hq
    exact criticalEvents_subset_canonicalCriticalEvents cs q
      ((mem_orderedUnique q (criticalEvents cs)).mp hq)
  exact Nat.le_trans
    (List.Nodup.length_le_of_subset (nodup_orderedUnique (criticalEvents cs)) hsub)
    (canonicalCriticalEvents_length_le cs)

/-! ### Winner changes and scan correctness through essential events -/

/-- Every actual successor winner change is an essential event. -/
theorem winner_change_forces_essentialEvent {cs : List Candidate} {t : Int}
    (hchange : ¬ SameWinnerSet cs (t + 1) t) :
    t + 1 ∈ essentialEvents cs :=
  mem_essentialEvents.mpr (winner_change_forces_event hchange)

/-- Event-scan segment exactness with the deduplicated event list. -/
theorem essential_scan_segment_exact {cs : List Candidate} {lo hi t : Int}
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ essentialEvents cs)
    (hlo : lo ≤ t) (hhi : t ≤ hi) :
    SameWinnerSet cs t lo := by
  apply critical_scan_segment_exact
  · intro q hqlo hqhi hqcritical
    exact hno q hqlo hqhi (mem_essentialEvents.mpr hqcritical)
  · exact hlo
  · exact hhi

/-- Pointwise event-scan correctness over essential events. -/
theorem essential_scan_winner_iff {cs : List Candidate} {lo hi t : Int}
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ essentialEvents cs)
    (hlo : lo ≤ t) (hhi : t ≤ hi) (c : Candidate) :
    Winner c cs t ↔ Winner c cs lo :=
  essential_scan_segment_exact hno hlo hhi c

/-- Event-start scan form, with the event at `lo` processed before the carry. -/
theorem essential_scan_event_winner_iff {cs : List Candidate} {lo hi t : Int}
    (_hloEvent : lo ∈ essentialEvents cs)
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ essentialEvents cs)
    (hlo : lo ≤ t) (hhi : t ≤ hi) (c : Candidate) :
    Winner c cs t ↔ Winner c cs lo :=
  essential_scan_winner_iff hno hlo hhi c

end AffineLifetime

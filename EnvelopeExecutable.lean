import EnvelopeEssentialEvents

/-!
## Executable essential-event envelope scan

This file turns the essential-event coverage theorem into a pure functional
scanner.  The scan receives a finite interval `[lo, hi]`, filters the essential
events to `(lo, hi]`, and emits one closed integer interval for every event
boundary (plus a final tail interval).  Each emitted segment stores the winner
computed at its left endpoint; the scanner therefore carries that candidate
across the whole segment.

The event semantics are boundary semantics: at every essential birth, death,
or affine crossing time, the scanner recomputes the pointwise winner.  No
event-kind-specific incremental update is required for exactness.

Tie handling is inherited from `AffRoute.wins`: endpoint equality is
non-strict, so exact ties can have several pointwise winners.  `winnerAt?`
chooses the first candidate in the input list that is a winner.  The main
theorems below prove that this chosen witness is exact on its emitted segment;
they do not claim uniqueness of the winner.
-/

namespace EnvelopeExecutable

open AffEnv
open AffineLifetime

/-! ### Executable winner selection -/

/-- Boolean form of affine lexicographic priority. -/
def winsBool (f g : AffRoute) (t : Int) : Bool :=
  decide (f.len t > g.len t) ||
    (decide (f.len t = g.len t) && decide (f.ep t ≥ g.ep t))

/-- `winsBool` reflects the existing affine priority relation. -/
theorem winsBool_eq_true_iff (f g : AffRoute) (t : Int) :
    winsBool f g t = true ↔ f.wins g t := by
  simp [winsBool, AffRoute.wins]

/-- Executable check that `c` is active and beats every active candidate. -/
def beatsAll (c : Candidate) (cs : List Candidate) (t : Int) : Bool :=
  cs.all (fun d => !decide (d.Active t) || winsBool c.route d.route t)

/-- Boolean dominance test reflects pointwise dominance over all active
candidates. -/
theorem beatsAll_eq_true_iff (c : Candidate) (cs : List Candidate) (t : Int) :
    beatsAll c cs t = true ↔
      ∀ d ∈ cs, d.Active t → c.route.wins d.route t := by
  simp only [beatsAll, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, winsBool_eq_true_iff]
  constructor
  · intro h d hd ha
    rcases h d hd with hna | hw
    · exact absurd ha hna
    · exact hw
  · intro h d hd
    by_cases ha : d.Active t
    · exact Or.inr (h d hd ha)
    · exact Or.inl ha

/-- Executable candidate-membership test, activity test, and dominance test. -/
def isWinner (c : Candidate) (cs : List Candidate) (t : Int) : Bool :=
  decide (c ∈ cs) && decide (c.Active t) && beatsAll c cs t

/-- Boolean winner test reflects the pointwise `Winner` predicate. -/
theorem isWinner_eq_true_iff (c : Candidate) (cs : List Candidate) (t : Int) :
    isWinner c cs t = true ↔ Winner c cs t := by
  unfold isWinner Winner
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    beatsAll_eq_true_iff]
  constructor
  · rintro ⟨⟨hmem, hact⟩, hbeats⟩
    exact ⟨hmem, hact, hbeats⟩
  · rintro ⟨hmem, hact, hbeats⟩
    exact ⟨⟨hmem, hact⟩, hbeats⟩

/-- Deterministic executable winner witness: first winner in candidate order. -/
def winnerAt? (cs : List Candidate) (t : Int) : Option Candidate :=
  cs.find? (fun c => isWinner c cs t)

/-- A returned winner is pointwise winning. -/
theorem winnerAt?_some_winner {cs : List Candidate} {t : Int} {w : Candidate}
    (h : winnerAt? cs t = some w) : Winner w cs t := by
  unfold winnerAt? at h
  exact (isWinner_eq_true_iff w cs t).mp
    (List.find?_some (p := fun c => isWinner c cs t) h)

/-- If no candidate is returned, then no candidate is a pointwise winner. -/
theorem winnerAt?_none_no_winner {cs : List Candidate} {t : Int}
    (h : winnerAt? cs t = none) : ∀ c, ¬ Winner c cs t := by
  intro c hc
  unfold winnerAt? at h
  have hnot := (List.find?_eq_none.mp h) c hc.1
  have hb : isWinner c cs t = true := (isWinner_eq_true_iff c cs t).mpr hc
  exact hnot hb

/-! ### Segment representation and scan -/

/-- One closed integer interval and its carried winner (if any). -/
structure Segment where
  lo : Int
  hi : Int
  carry : Option Candidate
  deriving DecidableEq, Repr

/-- Exactness contract for one scanner segment. -/
def SegmentExact (cs : List Candidate) (s : Segment) : Prop :=
  s.lo ≤ s.hi ∧
  (∀ w, s.carry = some w →
    Winner w cs s.lo ∧
    ∀ t, s.lo ≤ t → t ≤ s.hi → Winner w cs t) ∧
  (s.carry = none →
    ∀ t, s.lo ≤ t → t ≤ s.hi → ∀ c, ¬ Winner c cs t)

/-- Restrict an event list to `(lo, hi]`. -/
def boundedEvents (lo hi : Int) (events : List Int) : List Int :=
  events.filter (fun e => decide (lo < e ∧ e ≤ hi))

/-- Recursive scan over event boundaries.  The head `e` starts the next
segment; the previous segment ends at `e - 1`. -/
def scanAux (cs : List Candidate) (lo hi : Int) : List Int → List Segment
  | [] => [⟨lo, hi, winnerAt? cs lo⟩]
  | e :: es => ⟨lo, e - 1, winnerAt? cs lo⟩ :: scanAux cs e hi es

/-- Executable scan of the bounded essential-event list. -/
def scanEssential (cs : List Candidate) (lo hi : Int) : List Segment :=
  scanAux cs lo hi (boundedEvents lo hi (essentialEvents cs))

/-! ### Exactness of the scan -/

/-- Carry a winner across an event-free gap `(lo, hi]`. -/
theorem carry_some_exact {cs : List Candidate} {lo hi t : Int} {w : Candidate}
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ essentialEvents cs)
    (hcarry : winnerAt? cs lo = some w)
    (hlo : lo ≤ t) (hhi : t ≤ hi) : Winner w cs t :=
  (essential_scan_winner_iff hno hlo hhi w).mpr (winnerAt?_some_winner hcarry)

/-- Carry an empty winner across an event-free gap `(lo, hi]`. -/
theorem carry_none_exact {cs : List Candidate} {lo hi t : Int}
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ essentialEvents cs)
    (hcarry : winnerAt? cs lo = none)
    (hlo : lo ≤ t) (hhi : t ≤ hi) : ∀ c, ¬ Winner c cs t := by
  intro c hc
  exact winnerAt?_none_no_winner hcarry c
    ((essential_scan_winner_iff hno hlo hhi c).mp hc)

/-- An event-free interval is exact when its initial winner is carried. -/
theorem segment_exact_of_no_events {cs : List Candidate} {lo hi : Int}
    (hdom : lo ≤ hi)
    (hno : ∀ q, lo < q → q ≤ hi → q ∉ essentialEvents cs) :
    SegmentExact cs ⟨lo, hi, winnerAt? cs lo⟩ := by
  unfold SegmentExact
  constructor
  · exact hdom
  constructor
  · intro w hw
    constructor
    · exact winnerAt?_some_winner hw
    · intro t htlo hthi
      exact carry_some_exact hno hw htlo hthi
  · intro hw t htlo hthi c hc
    exact carry_none_exact hno hw htlo hthi c hc

/-- Core exactness theorem for the recursive boundary scan.

`hSorted` supplies ascending event order.  `hComplete` states that the input
event list contains every essential event in `(lo, hi]`; this is the coverage
assumption used to locate the next possible winner change. -/
theorem scanAux_exact {cs : List Candidate} {lo hi : Int} {events : List Int}
    (hdom : lo ≤ hi)
    (hSorted : events.Pairwise (· < ·))
    (hLower : ∀ e, e ∈ events → lo < e)
    (hUpper : ∀ e, e ∈ events → e ≤ hi)
    (hComplete : ∀ q, lo < q → q ≤ hi → q ∈ essentialEvents cs → q ∈ events)
    {s : Segment} (hs : s ∈ scanAux cs lo hi events) :
    SegmentExact cs s := by
  induction events generalizing lo with
  | nil =>
      simp only [scanAux, List.mem_singleton] at hs
      subst s
      apply segment_exact_of_no_events hdom
      intro q hqlo hqhi hq
      have hqmem : q ∈ ([] : List Int) := hComplete q hqlo hqhi hq
      simp at hqmem
  | cons e es ih =>
      simp only [List.pairwise_cons] at hSorted
      simp only [scanAux, List.mem_cons] at hs
      rcases hs with hs | hs
      · subst s
        apply segment_exact_of_no_events
        · have he : lo < e := hLower e (by simp)
          omega
        · intro q hqlo hqle hqess
          have hehi : e ≤ hi := hUpper e (by simp)
          have hqhi : q ≤ hi := by omega
          have hqmem : q ∈ e :: es := hComplete q hqlo hqhi hqess
          have hqes : q ∈ es := by
            rcases List.mem_cons.mp hqmem with hqe | hqes
            · subst q
              omega
            · exact hqes
          have heq : e < q := hSorted.1 q hqes
          omega
      · exact ih (lo := e)
          (hUpper e (by simp))
          hSorted.2
          (fun q hq => by
            have heq : e < q := hSorted.1 q hq
            omega)
          (fun q hq => hUpper q (by simp [hq]))
          (fun q hqe hqhi hqess => by
            have hlo_e : lo < e := hLower e (by simp)
            have hlo_q : lo < q := by omega
            have hqmem : q ∈ e :: es := hComplete q hlo_q hqhi hqess
            rcases List.mem_cons.mp hqmem with hqeq | hqes
            · omega
            · exact hqes)
          hs

/-- Exactness of the executable scan of `(lo, hi]`.  The only structural
assumption on the essential-event list is ascending order; boundedness and
coverage are established by `boundedEvents`. -/
theorem scanEssential_exact {cs : List Candidate} {lo hi : Int}
    (hdom : lo ≤ hi)
    (hSorted : (essentialEvents cs).Pairwise (· < ·))
    {s : Segment} (hs : s ∈ scanEssential cs lo hi) :
    SegmentExact cs s := by
  unfold scanEssential boundedEvents at hs
  apply scanAux_exact hdom
  · exact List.Pairwise.filter (fun e => decide (lo < e ∧ e ≤ hi)) hSorted
  · intro e he
    have hp := (List.mem_filter.mp he).2
    exact (of_decide_eq_true hp).1
  · intro e he
    have hp := (List.mem_filter.mp he).2
    exact (of_decide_eq_true hp).2
  · intro q hqlo hqhi hq
    exact List.mem_filter.mpr ⟨hq, decide_eq_true ⟨hqlo, hqhi⟩⟩
  · exact hs

/-- The scanned segments cover every integer time in `[lo, hi]`. -/
theorem scanAux_covers {cs : List Candidate} {lo hi t : Int} {events : List Int}
    (hSorted : events.Pairwise (· < ·))
    (hLower : ∀ e, e ∈ events → lo < e)
    (hUpper : ∀ e, e ∈ events → e ≤ hi)
    (htlo : lo ≤ t) (hthi : t ≤ hi) :
    ∃ s, s ∈ scanAux cs lo hi events ∧ s.lo ≤ t ∧ t ≤ s.hi := by
  induction events generalizing lo with
  | nil =>
      refine ⟨⟨lo, hi, winnerAt? cs lo⟩, by simp [scanAux], htlo, hthi⟩
  | cons e es ih =>
      have he_le : e ≤ hi := hUpper e (by simp)
      by_cases ht : t ≤ e - 1
      · refine ⟨⟨lo, e - 1, winnerAt? cs lo⟩, by simp [scanAux], htlo, ht⟩
      · have het : e ≤ t := by omega
        simp only [List.pairwise_cons] at hSorted
        rcases ih (lo := e)
          hSorted.2
          (fun q hq => hSorted.1 q hq)
          (fun q hq => hUpper q (by simp [hq]))
          het with ⟨s, hs, hslo, hshi⟩
        exact ⟨s, by simp [scanAux, hs], hslo, hshi⟩

/-- The executable essential scan covers `[lo, hi]`. -/
theorem scanEssential_covers {cs : List Candidate} {lo hi t : Int}
    (hSorted : (essentialEvents cs).Pairwise (· < ·))
    (htlo : lo ≤ t) (hthi : t ≤ hi) :
    ∃ s, s ∈ scanEssential cs lo hi ∧ s.lo ≤ t ∧ t ≤ s.hi := by
  unfold scanEssential boundedEvents
  apply scanAux_covers
  · exact List.Pairwise.filter (fun e => decide (lo < e ∧ e ≤ hi)) hSorted
  · intro e he
    have hp := (List.mem_filter.mp he).2
    exact (of_decide_eq_true hp).1
  · intro e he
    have hp := (List.mem_filter.mp he).2
    exact (of_decide_eq_true hp).2
  · exact htlo
  · exact hthi

/-- Convenient pointwise form: a `some` carry in an emitted segment is a
pointwise winner throughout that segment. -/
theorem scanEssential_some_winner {cs : List Candidate} {lo hi t : Int}
    (hdom : lo ≤ hi)
    (hSorted : (essentialEvents cs).Pairwise (· < ·))
    {s : Segment} (hs : s ∈ scanEssential cs lo hi)
    (hcarry : s.carry = some w) (htlo : s.lo ≤ t) (hthi : t ≤ s.hi) :
    Winner w cs t :=
  (scanEssential_exact hdom hSorted hs).2.1 w hcarry |>.2 t htlo hthi

/-- Convenient pointwise form: a `none` carry means no pointwise winner in
that emitted segment. -/
theorem scanEssential_none_no_winner {cs : List Candidate} {lo hi t : Int}
    (hdom : lo ≤ hi)
    (hSorted : (essentialEvents cs).Pairwise (· < ·))
    {s : Segment} (hs : s ∈ scanEssential cs lo hi)
    (hcarry : s.carry = none) (htlo : s.lo ≤ t) (hthi : t ≤ s.hi)
    (c : Candidate) : ¬ Winner c cs t :=
  (scanEssential_exact hdom hSorted hs).2.2 hcarry t htlo hthi c

/-! ### Event coverage and output size -/

/-- Every actual winner change is a boundary in the executable scan whenever
the change lies in the scanned half-open range `(lo, hi]`. -/
theorem scanEssential_change_mem_boundaries {cs : List Candidate} {lo hi t : Int}
    (hchange : ¬ SameWinnerSet cs (t + 1) t)
    (hlo : lo < t + 1) (hhi : t + 1 ≤ hi) :
    t + 1 ∈ boundedEvents lo hi (essentialEvents cs) := by
  exact List.mem_filter.mpr
    ⟨winner_change_forces_essentialEvent hchange, decide_eq_true ⟨hlo, hhi⟩⟩

/-- The recursive scanner emits exactly one segment per boundary plus a tail. -/
theorem scanAux_length (cs : List Candidate) (lo hi : Int) (events : List Int) :
    (scanAux cs lo hi events).length = events.length + 1 := by
  induction events generalizing lo with
  | nil => simp [scanAux]
  | cons e es ih => simp [scanAux, ih]

/-- Output-size expression for the executable essential-event scan. -/
theorem scanEssential_length (cs : List Candidate) (lo hi : Int) :
    (scanEssential cs lo hi).length =
      (boundedEvents lo hi (essentialEvents cs)).length + 1 := by
  unfold scanEssential
  exact scanAux_length cs lo hi (boundedEvents lo hi (essentialEvents cs))

end EnvelopeExecutable

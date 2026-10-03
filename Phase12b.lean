import Std
import Route
import OwnerCompress
import CommonBirth
import KSkyline
import RosBridge
import WinnerPieces
import Gluing

/-!
## Phase H — step 12b: size / piece-count

Per the 12b guide the right move is **not** to count polyline intersections but to
count *no re-entry* of the winner:

* candidates are already bounded: `|flatten(C₁..C_m)| ≤ 3m` (each block ≤ 3);
* the real content is `#winner segments` — which follows **purely
  combinatorially** once each label's winner set is an interval (no re-entry).

This file closes the generic part (the guide's §3/§13).  The later
`BlockWinnerNoReentry`, `OwnerKBaselineEnvelope`, and `EnvelopeExecutable`
modules resolve the fixed-owner lifetime cases and prove a counterexample to the
unconditional cross-block claim.  Global `≤3m` therefore remains conditional on
explicit cross-block interval/coverage hypotheses.
-/

namespace Phase12b
open Route OwnerCompress OwnerCorrect OwnerCorrectK WinnerPieces Gluing
open RosBridge CommonBirth KSkyline KDeleteAbstract

/-! ### The generic combinatorial core (§2, §3, §13) -/

/-- Collapse adjacent duplicates — i.e. the **maximal constant segments**. -/
def compress {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
      if a = b then compress (b :: rest)
      else a :: compress (b :: rest)

/-- `compress` only deletes elements, so it is a sublist. -/
theorem compress_sublist {α : Type} [DecidableEq α] (l : List α) : List.Sublist (compress l) l := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a rest ih =>
    cases rest with
    | nil => exact List.Sublist.cons_cons a List.Sublist.slnil
    | cons b rest' =>
      simp only [compress]
      by_cases hab : a = b
      · rw [if_pos hab]; exact List.Sublist.cons a ih
      · rw [if_neg hab]; exact List.Sublist.cons_cons a ih

/-- **No re-entry** (§2): after collapsing adjacent duplicates no label recurs —
equivalently every label occupies a single contiguous run. -/
def NoReentry {α : Type} [DecidableEq α] (l : List α) : Prop := (compress l).Nodup

/-- **§3 pigeonhole.**  A no-re-entry sequence has at most as many maximal
constant segments as the size of any list containing all its labels. -/
theorem segments_le_of_subset {α : Type} [DecidableEq α] {l s : List α}
    (h : NoReentry l) (hsub : ∀ a ∈ l, a ∈ s) : (compress l).length ≤ s.length :=
  List.Nodup.length_le_of_subset h (fun a ha => hsub a ((compress_sublist l).subset ha))

/-! ### §20 candidate bound -/

/-- **§13 `field_flatten_length_le`.**  A multi-run IR of blocks each holding at
most three candidates has at most `3m` candidates. -/
theorem flatten_length_le {α : Type} {blocks : List (List α)}
    (h : ∀ b ∈ blocks, b.length ≤ 3) : blocks.flatten.length ≤ 3 * blocks.length := by
  induction blocks with
  | nil => simp
  | cons b bs ih =>
    rw [List.flatten_cons, List.length_append, List.length_cons]
    have hb : b.length ≤ 3 := h b (by simp)
    have hbs : bs.flatten.length ≤ 3 * bs.length := ih (fun b' hb' => h b' (by simp [hb']))
    omega

/-! ### §13 the combined size theorem -/

/-- **§13 `field_winner_segment_count_le` (conditional form).**  Given
(i) every block holds `≤ 3` candidates and (ii) the winner sequence over the
flattened candidates has no re-entry, the number of maximal winner segments is
at most `3m`.  **Exact bound, no Big-O.** -/
theorem segments_le_three_mul {α : Type} [DecidableEq α] {blocks : List (List α)} {l : List α}
    (hlen : ∀ b ∈ blocks, b.length ≤ 3) (h : NoReentry l)
    (hsub : ∀ a ∈ l, a ∈ blocks.flatten) :
    (compress l).length ≤ 3 * blocks.length := by
  have h1 := segments_le_of_subset h hsub
  have h2 := flatten_length_le hlen
  omega

/-! ### Resolution of the former block-level obligation

The unconditional global claim is false: `BlockWinnerNoReentry` constructs a
canonical-identity re-entry across competing blocks.  The correct fixed-owner
theory is proved in `OwnerKBaselineEnvelope` and `OwnerWindowDischarge`; global
bounds are conditional on `CrossBlockIdentityIntervals` and active coverage.
This file's combinatorial theorem remains the closing pigeonhole step once those
hypotheses are supplied.

Brute-force findings (research/research_rosa/bruteforce_12b.py, 117376 cases: T≤8
exhaustive + T≤16 random), **repair bridges only, per owner** (owners do not
compete):

* **Q side: canonical-identity no-re-entry holds** (0 violations) — consistent
  with `common_birth_winner_iff` (common birth ⇒ expiry skyline).
* **K side: canonical-identity no-re-entry FAILS without the deletion
  baseline** (6594 violations); first counterexample
  `q=000110, k=010100` owner `u=2`, identity sequence
  `(3,2) (4,2) (3,2)`.  So the K-side obligation **must** be stated over
  `rosaKDelete` (guide §26: "K side keeps the deletion baseline"), exactly as
  `KSkyline.k_suffix_winner_iff` does.
* **The *route-value* sequence is NOT no-re-entry even on the Q side**
  (first: `q=001110, k=010000`, `(3,2) (2,1) (3,2)`: two *different* candidates
  emit the same `(3,2)` at t=3 and t=5).  So guide §3's `#segments ≤ #candidates`
  holds for the **canonical identity**, **not** for the raw output value; the
  "affine pieces" count of the emitted route is a *different* quantity.
-/

/-! ### §2 interval ⇒ no re-entry ⇒ `#segments ≤ 3m` (the closing step)

The brute-force search (see README) showed that the correct no-re-entry object is
the **canonical winner identity**, and that each candidate's *winner set* is an
interval (Q: `common_birth_winner_iff`; K: `k_suffix_winner_iff`).  Here we turn
"interval winner set" directly into the segment bound, with no `compress` glue.
-/

/-- A subset of `Nat` is an **interval** (order-convex). -/
def IsInterval (S : Nat → Prop) : Prop :=
  ∀ i, S i → ∀ k, S k → ∀ j, i ≤ j → j ≤ k → S j

/-- `t` opens a new segment of the winner-identity sequence `f`. -/
def IsSegStart {α : Type} [DecidableEq α] (f : Nat → α) (t : Nat) : Prop :=
  t = 0 ∨ f t ≠ f (t - 1)

instance {α : Type} [DecidableEq α] (f : Nat → α) (t : Nat) : Decidable (IsSegStart f t) := by
  unfold IsSegStart; infer_instance

/-- **Bridging lemma (guide §2).**  If every label's winner-set is an interval,
two distinct segment starts carry distinct labels — the canonical winner identity
never re-enters. -/
theorem segStart_label_ne {α : Type} [DecidableEq α] {f : Nat → α}
    (h : ∀ c, IsInterval (fun t => f t = c)) {t₁ t₂ : Nat}
    (h₂ : IsSegStart f t₂) (hlt : t₁ < t₂) : f t₁ ≠ f t₂ := by
  intro heq
  have hne : f t₂ ≠ f (t₂ - 1) := by
    rcases h₂ with h0 | h0
    · omega
    · exact h0
  exact hne (h (f t₂) t₁ heq t₂ rfl (t₂ - 1) (by omega) (by omega)).symm

/-- `map` preserves `Nodup` when `f` is injective *on the list*. -/
theorem nodup_map_of_pairwise_inj {αs βs : Type} {f : αs → βs} {l : List αs}
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (hnd : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy]))
      (List.nodup_cons.mp hnd).2⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨b, hb, hba⟩ := hmem
    exact (List.nodup_cons.mp hnd).1 (by rw [hinj a (by simp) b (by simp [hb]) hba.symm]; exact hb)

theorem segStarts_le_of_subset {α : Type} [DecidableEq α] (f : Nat → α) {T : Nat} {s : List α}
    (h : ∀ c, IsInterval (fun t => f t = c)) (hsub : ∀ t, t < T → f t ∈ s) :
    ((List.range T).filter (fun t => decide (IsSegStart f t))).length ≤ s.length := by
  have hnd : ((List.range T).filter (fun t => decide (IsSegStart f t))).Nodup :=
    List.Nodup.sublist (List.filter_sublist (p := fun t => decide (IsSegStart f t)))
      List.nodup_range
  have hinj : ∀ a ∈ (List.range T).filter (fun t => decide (IsSegStart f t)),
      ∀ b ∈ (List.range T).filter (fun t => decide (IsSegStart f t)), f a = f b → a = b := by
    intro a ha b hb hab
    by_cases hlt : a < b
    · exact absurd hab (segStart_label_ne h (of_decide_eq_true (List.mem_filter.mp hb).2) hlt)
    · have hle : b ≤ a := Nat.le_of_not_lt hlt
      by_cases hgt : b < a
      · exact absurd hab.symm (segStart_label_ne h (of_decide_eq_true (List.mem_filter.mp ha).2) hgt)
      · omega
  have hsub2 : ∀ c ∈ (List.range T).filter (fun t => decide (IsSegStart f t)) |>.map f, c ∈ s := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact hsub t (List.mem_range.mp (List.mem_filter.mp ht).1)
  have := List.Nodup.length_le_of_subset (nodup_map_of_pairwise_inj hinj hnd) hsub2
  rwa [List.length_map] at this

/-- **§13 closing theorem (guide §2/§3).**  Given (i) every block holds `≤ 3`
candidates, (ii) every winner-label's preimage is an interval, and (iii) winners
are drawn from the blocks — the number of winner segments is at most `3m`.
**Exact bound, no Big-O, no polyline-intersection counting.** -/
theorem segments_le_three_mul_of_isInterval {α : Type} [DecidableEq α]
    {blocks : List (List α)} (f : Nat → α) {T : Nat}
    (hlen : ∀ b ∈ blocks, b.length ≤ 3)
    (hint : ∀ c, IsInterval (fun t => f t = c))
    (hsub : ∀ t, t < T → f t ∈ blocks.flatten) :
    ((List.range T).filter (fun t => decide (IsSegStart f t))).length ≤ 3 * blocks.length := by
  have h1 := segStarts_le_of_subset f hint hsub
  have h2 := flatten_length_le hlen
  omega

/-! ### Discharging the interval hypothesis from the ROSA layer -/

/-- **Q side.**  A common-birth candidate's winner set is an interval
(`CommonBirth.common_birth_winner_iff`). -/
theorem qCBCand_isInterval {p : Nat} (cs : List CBCand) (c : CBCand) :
    IsInterval (fun t => cbWins p cs c t) := by
  intro i hi k hk j hij hjk
  rw [common_birth_winner_iff] at hi hk ⊢
  exact ⟨Nat.le_trans hi.1 hij, Nat.le_trans hjk hk.2⟩

/-- **K side.**  The K-suffix winner set is an interval
(`KSkyline.k_suffix_winner_iff`) — this is the deletion-baseline-aware winner, as
the brute-force search demands. -/
theorem kSuffixWinner_isInterval {D : KDeleteFamily} {others : List Bridge} {b : Bridge}
    (htrim : TrimClosed D)
    (hshadow : ∀ c ∈ others, klexLT c.kappa b.kappa → HasPrebirthShadow D c)
    (hreach : ∀ c ∈ others, klexLT c.kappa b.kappa → c.shadowStart ≤ (b.p : Int))
    {d M : Nat} (hdlow : ∀ t, b.p ≤ t → t < d → ¬ D.Beats b t)
    (hdhigh : ∀ t, d ≤ t → t ≤ b.death → D.Beats b t)
    (hM : ∀ c ∈ others, klexLT c.kappa b.kappa → c.death ≤ M)
    (hMat : M < b.p ∨ ∃ c ∈ others, klexLT c.kappa b.kappa ∧ c.death = M) :
    IsInterval (fun t => b.Active t ∧ D.Beats b t ∧ ∀ c ∈ others, c.Active t → ¬ klexLT c.kappa b.kappa) := by
  intro i hi k hk j hij hjk
  rw [k_suffix_winner_iff htrim hshadow hreach hdlow hdhigh hM hMat] at hi hk ⊢
  exact ⟨Nat.le_trans hi.1 hij, Nat.le_trans hjk hk.2⟩

/-! ### §1/§2 one bridge = one affine piece (the correct index)

The brute-force counterexample `(3,2) (2,1) (3,2)` is *irrelevant*: a single bridge
living T steps already yields T different **Route values**, e.g.
`route_b(t) = (t+α, t+β)`.  The right quantity is the **affine piece** count, and
every repair bridge has slope `(1,1)`:

  `route_b(t) = (t + α_b, t + β_b)`,  `α_b = L+1-p`, `β_b = u-p`.

Equivalently, in `κ` coordinates `κ = (a, -s)`:
  `routeOfKappa κ t = (t - a + 1, t + s - 1)`.

So an interval winner set `[g, e]` is **one** affine piece, independent of how many
distinct Route values appear inside it.
-/

/-- The affine route with priority `κ`. -/
def routeOfKappa (k : Int × Int) (t : Nat) : Route :=
  ⟨(t : Int) - k.1 + 1, (t : Int) - k.2 - 1⟩

/-- **`bridge_route_affine` (§1).**  `κ` determines the whole affine route; a bridge
is *exactly* the slope-`(1,1)` line of its `κ`. -/
theorem bridge_route_eq_routeOfKappa (b : Bridge) (t : Nat) (h : b.Active t) :
    b.routeAt t = routeOfKappa b.kappa t := by
  obtain ⟨hb1, _⟩ := h
  apply Route.ext
  · show ((b.L + 1 + (t - b.p) : Nat) : Int) = (t : Int) - ((b.p : Int) - (b.L : Int)) + 1
    have hc : ((b.L + 1 + (t - b.p) : Nat) : Int)
        = (b.L : Int) + 1 + ((t : Int) - (b.p : Int)) := by omega
    rw [hc]; omega
  · show ((b.u + (t - b.p) : Nat) : Int) = (t : Int) - (-(((b.u : Int) - (b.p : Int)) + 1)) - 1
    have hc : ((b.u + (t - b.p) : Nat) : Int)
        = (b.u : Int) + ((t : Int) - (b.p : Int)) := by omega
    rw [hc]; omega

/-- Slope is `(1,1)`: `len(t) − t` and `endpoint(t) − t` are the constants `α, β`. -/
theorem bridge_route_affine (b : Bridge) (t : Nat) (h : b.Active t) :
    (b.routeAt t).len = (t : Int) + (-b.kappa.1 + 1) ∧
      (b.routeAt t).endpoint = (t : Int) + (-b.kappa.2 - 1) := by
  rw [bridge_route_eq_routeOfKappa b t h]
  exact ⟨by simp only [routeOfKappa]; omega, by simp only [routeOfKappa]; omega⟩

/-- `κ` determines the affine route function (no two distinct `κ` share a line). -/
theorem routeOfKappa_inj {k₁ k₂ : Int × Int}
    (h : ∀ t, routeOfKappa k₁ t = routeOfKappa k₂ t) : k₁ = k₂ := by
  have h0 : -k₁.1 + 1 = -k₂.1 + 1 := by
    have := congrArg Route.len (h 0); simpa [routeOfKappa] using this
  have h1 : -k₁.2 - 1 = -k₂.2 - 1 := by
    have := congrArg Route.endpoint (h 0); simpa [routeOfKappa] using this
  exact Prod.ext (by omega) (by omega)

/-- `F` agrees with the affine route of `κ` on `[lo, hi]` — **one affine piece**. -/
def AffineOn (F : Nat → Route) (k : Int × Int) (lo hi : Nat) : Prop :=
  ∀ t, lo ≤ t → t ≤ hi → F t = routeOfKappa k t

/-- **A bridge is one affine piece** over its whole lifetime. -/
theorem bridge_affineOn (b : Bridge) : AffineOn b.routeAt b.kappa b.p (b.p + b.R) :=
  fun t h1 h2 => bridge_route_eq_routeOfKappa b t ⟨h1, h2⟩

/-! ### §13 overlay bound: `Pieces ≤ q + 2r` (generic, ROSA-free) -/

/-- Breakpoints contributed by `r` overlay intervals. -/
def bpsOf (R : List (Nat × Nat)) : List Nat := R.flatMap (fun p => [p.1, p.2])

theorem bpsOf_length_le (R : List (Nat × Nat)) : (bpsOf R).length ≤ 2 * R.length := by
  induction R with
  | nil => simp [bpsOf]
  | cons p ps ih =>
    simp only [bpsOf, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
    omega

/-- **`piece_count_overlay_le` (§13).**  A base with `q` pieces, overlaid by `r`
repair intervals, has at most `q + 2r` pieces: one baseline piece is cut into at
most three (`+2` breakpoints per interval).  The bound is tight in the abstract
(`D B D B … D` gives `2r+1 = q + 2r`).  **Storing the overlay un-materialised**
costs only `q + r`. -/
theorem overlay_breakpoints_le (base : List Nat) (R : List (Nat × Nat)) :
    (base ++ bpsOf R).length ≤ base.length + 2 * R.length := by
  rw [List.length_append]
  have := bpsOf_length_le R
  omega

end Phase12b

import PayloadContraction

/-!
## Error bounds for the M4 payload contraction

This file adds an abstract approximate-value layer on top of the exact integer
algebra in `PayloadContraction`.  An `Approx` is an integer representative
together with an explicit natural error budget.  The predicate `CloseTo` states
that the representative differs from a supplied exact integer by at most that
budget.

No theorem below asserts a particular `Float32` or `Float64` semantics.  In
particular, it does not assume that floating-point addition is associative or
that a runtime dot product has any prescribed reduction order.  Runtime code
must supply the pointwise error hypotheses and the concrete `RoundingBudget`
values, or separately instantiate them with a verified floating-point model.
-/

namespace PayloadErrorBound

open PayloadContraction

/-- An integer approximation together with an explicit error upper bound. -/
structure Approx where
  value : Int
  error : Nat
  deriving Repr, DecidableEq

/-- An approximate integer is `CloseTo` the exact integer when its distance is
at most the declared error budget. -/
def Approx.CloseTo (a : Approx) (x : Int) : Prop :=
  Int.natAbs (a.value - x) ≤ a.error

/-- An exact integer represented with zero error. -/
def Approx.exact (x : Int) : Approx :=
  { value := x, error := 0 }

/-- Explicit budgets for rounded primitive operations.  The fields are
independent so that a concrete Float model can instantiate only the operations
it actually uses. -/
structure RoundingBudget where
  add : Nat := 0
  sub : Nat := 0
  mul : Nat := 0
  deriving Repr, DecidableEq

namespace RoundingBudget

/-- The exact-arithmetic budget. -/
def zero : RoundingBudget :=
  { add := 0, sub := 0, mul := 0 }

end RoundingBudget

namespace Approx

/-- Rounded addition of two approximate integers. -/
def add (a b : Approx) (r : RoundingBudget) : Approx :=
  { value := a.value + b.value
    error := a.error + b.error + r.add }

/-- Rounded subtraction of two approximate integers. -/
def sub (a b : Approx) (r : RoundingBudget) : Approx :=
  { value := a.value - b.value
    error := a.error + b.error + r.sub }

/-- Rounded multiplication by a supplied exact integer coefficient.  This is
the only multiplication primitive used by the contraction bounds below: the
runtime gradient is treated as an exact integer coefficient at this layer. -/
def mulConst (a : Approx) (c : Int) (r : RoundingBudget) : Approx :=
  { value := c * a.value
    error := c.natAbs * a.error + r.mul }

end Approx

theorem add_close (a b : Approx) (x y : Int) (r : RoundingBudget)
    (ha : a.CloseTo x) (hb : b.CloseTo y) :
    (a.add b r).CloseTo (x + y) := by
  change Int.natAbs (a.value - x) ≤ a.error at ha
  change Int.natAbs (b.value - y) ≤ b.error at hb
  change Int.natAbs ((a.value + b.value) - (x + y)) ≤
    a.error + b.error + r.add
  have hdiff : a.value + b.value - (x + y) = (a.value - x) + (b.value - y) := by
    omega
  rw [hdiff]
  exact Nat.le_trans (Int.natAbs_add_le (a.value - x) (b.value - y)) (by omega)

theorem sub_close (a b : Approx) (x y : Int) (r : RoundingBudget)
    (ha : a.CloseTo x) (hb : b.CloseTo y) :
    (a.sub b r).CloseTo (x - y) := by
  change Int.natAbs (a.value - x) ≤ a.error at ha
  change Int.natAbs (b.value - y) ≤ b.error at hb
  change Int.natAbs ((a.value - b.value) - (x - y)) ≤
    a.error + b.error + r.sub
  have hdiff : a.value - b.value - (x - y) = (a.value - x) - (b.value - y) := by
    omega
  rw [hdiff]
  exact Nat.le_trans (Int.natAbs_sub_le (a.value - x) (b.value - y)) (by omega)

theorem mulConst_close (a : Approx) (x : Int) (c : Int) (r : RoundingBudget)
    (ha : a.CloseTo x) :
    (a.mulConst c r).CloseTo (c * x) := by
  change Int.natAbs (a.value - x) ≤ a.error at ha
  change Int.natAbs (c * a.value - c * x) ≤ c.natAbs * a.error + r.mul
  have hdiff : c * a.value - c * x = c * (a.value - x) := by
    rw [Int.mul_sub]
  rw [hdiff, Int.natAbs_mul]
  exact Nat.le_trans (Nat.mul_le_mul_left c.natAbs ha) (by omega)

/-! ## Finite interval error accumulation -/

/-- Sum of a `Nat`-valued sequence over the first `n` positions starting at
`lo`.  This is the error-budget counterpart of the exclusive prefix sum. -/
def natIntervalSum (f : Nat → Nat) (lo : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natIntervalSum f lo n + f (lo + n)

@[simp] theorem natIntervalSum_zero (f : Nat → Nat) (lo : Nat) :
    natIntervalSum f lo 0 = 0 := rfl

@[simp] theorem natIntervalSum_succ (f : Nat → Nat) (lo n : Nat) :
    natIntervalSum f lo (n + 1) = natIntervalSum f lo n + f (lo + n) := rfl

/-- The total declared error on an inclusive interval `[lo, hi]`. -/
def errorIntervalSum (f : Nat → Approx) (lo hi : Nat) : Nat :=
  natIntervalSum (fun t => (f t).error) lo (hi + 1 - lo)

/-- The natural-number interval length of an inclusive interval, with the
degenerate out-of-order case mapped to zero. -/
def intervalLength (lo hi : Nat) : Nat :=
  hi + 1 - lo

@[simp] theorem intervalLength_eq (lo hi : Nat) :
    intervalLength lo hi = hi + 1 - lo := rfl

/-- Triangle inequality for an inclusive interval sum: the absolute value of a
sum is bounded by the sum of the pointwise absolute values.  The statement is
indexed by a length `n`, which avoids subtraction in the induction. -/
theorem natAbs_intervalSum_le_range (w : Nat → Int) (e : Nat → Nat)
    (lo n : Nat)
    (h : ∀ k, k < n + 1 → Int.natAbs (w (lo + k)) ≤ e (lo + k)) :
    Int.natAbs (intervalSum w lo (lo + n)) ≤
      natIntervalSum e lo (n + 1) := by
  induction n with
  | zero =>
      simpa [Nat.add_zero, intervalSum_singleton, natIntervalSum_succ] using
        h 0 (by omega)
  | succ n ih =>
      have hconcat := intervalSum_concat w lo (lo + n) (lo + n + 1)
      have hidx : lo + (n + 1) = (lo + n) + 1 := by omega
      rw [hidx, ← hconcat]
      have ih' := ih (fun k hk => h k (by omega))
      have hsingle : Int.natAbs (intervalSum w (lo + n + 1) (lo + n + 1)) ≤
          e (lo + n + 1) := by
        rw [intervalSum_singleton]
        exact h (n + 1) (by omega)
      calc
        Int.natAbs (intervalSum w lo (lo + n) +
            intervalSum w (lo + n + 1) (lo + n + 1))
            ≤ Int.natAbs (intervalSum w lo (lo + n)) +
                Int.natAbs (intervalSum w (lo + n + 1) (lo + n + 1)) :=
              Int.natAbs_add_le _ _
        _ ≤ natIntervalSum e lo (n + 1) + e (lo + n + 1) :=
              Nat.add_le_add ih' hsingle
        _ = natIntervalSum e lo (n + 1 + 1) := by
              simp only [natIntervalSum_succ, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]

/-- Interval-sum form of the triangle inequality, with the span written as
`hi - lo`. -/
theorem natAbs_intervalSum_le (w : Nat → Int) (e : Nat → Nat)
    (lo hi : Nat) (hle : lo ≤ hi)
    (h : ∀ t, lo ≤ t → t ≤ hi → Int.natAbs (w t) ≤ e t) :
    Int.natAbs (intervalSum w lo hi) ≤
      natIntervalSum e lo (hi + 1 - lo) := by
  have hlo : lo + (hi - lo) = hi := by omega
  have hrange :
      ∀ k, k < (hi - lo) + 1 →
        Int.natAbs (w (lo + k)) ≤ e (lo + k) := by
    intro k hk
    exact h (lo + k) (by omega) (by omega)
  have hbound := natAbs_intervalSum_le_range w e lo (hi - lo) hrange
  have hlen : hi - lo + 1 = hi + 1 - lo := by omega
  simpa [hlo, hlen] using hbound

/-- An exact inclusive sum of approximate values, together with the accumulated
input-error budget and a length-scaled addition-rounding budget. -/
def approxIntervalSum (f : Nat → Approx) (r : RoundingBudget)
    (lo hi : Nat) : Approx :=
  { value := intervalSum (fun t => (f t).value) lo hi
    error := errorIntervalSum f lo hi + r.add * intervalLength lo hi }

/-- Propagation theorem for an inclusive interval sum.  Each point contributes
its declared error; the additional `r.add * (hi + 1 - lo)` term is the explicit
summation-rounding allowance. -/
theorem approxIntervalSum_close (f : Nat → Approx) (x : Nat → Int)
    (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (h : ∀ t, lo ≤ t → t ≤ hi → (f t).CloseTo (x t)) :
    (approxIntervalSum f r lo hi).CloseTo (intervalSum x lo hi) := by
  change Int.natAbs
      (intervalSum (fun t => (f t).value) lo hi - intervalSum x lo hi)
    ≤ errorIntervalSum f lo hi + r.add * intervalLength lo hi
  rw [← intervalSum_sub]
  have hpoint : ∀ t, lo ≤ t → t ≤ hi →
      Int.natAbs ((f t).value - x t) ≤ (f t).error := by
    intro t htlo hthi
    exact h t htlo hthi
  have htri := natAbs_intervalSum_le
    (fun t => (f t).value - x t) (fun t => (f t).error) lo hi hle hpoint
  exact Nat.le_trans htri (by
    unfold errorIntervalSum intervalLength
    exact Nat.le_add_right _ _)

/-- The explicit error component of an approximate interval sum. -/
theorem approxIntervalSum_error_eq (f : Nat → Approx) (r : RoundingBudget)
    (lo hi : Nat) :
    (approxIntervalSum f r lo hi).error =
      errorIntervalSum f lo hi + r.add * intervalLength lo hi := rfl

/-- Exact zero-error approximation is close to its exact value. -/
theorem Approx.exact_close (x : Int) : (Approx.exact x).CloseTo x := by
  simp [Approx.exact, Approx.CloseTo]

/-- Pointwise closeness for two equal-length lists. -/
inductive PointwiseClose : List Approx → List Int → Prop
  | nil : PointwiseClose [] []
  | cons {a : Approx} {x : Int} {as : List Approx} {xs : List Int}
      (ha : a.CloseTo x) (ht : PointwiseClose as xs) :
      PointwiseClose (a :: as) (x :: xs)

/-- Accumulate a list of approximate values from left to right. -/
def approxListSum (r : RoundingBudget) : List Approx → Approx
  | [] => Approx.exact 0
  | a :: as => a.add (approxListSum r as) r

/-- The value component of a list accumulation is exactly the list sum of all
value components.  The rounding budget affects only the error component. -/
theorem approxListSum_value_eq (r : RoundingBudget) (xs : List Approx) :
    (approxListSum r xs).value = (xs.map (fun a => a.value)).sum := by
  induction xs with
  | nil => simp [approxListSum, Approx.exact]
  | cons a as ih => simp [approxListSum, Approx.add, ih]

/-- Error propagation for a list accumulation. -/
theorem approxListSum_close (r : RoundingBudget) {xs : List Approx}
    {ys : List Int} (h : PointwiseClose xs ys) :
    (approxListSum r xs).CloseTo ys.sum := by
  induction h with
  | nil => simpa [approxListSum] using Approx.exact_close 0
  | cons ha ht ih =>
      simpa [approxListSum, List.sum_cons] using
        add_close _ _ _ _ r ha ih

/-- Explicit error budget for a list accumulation. -/
theorem approxListSum_error_bound (r : RoundingBudget) (xs : List Approx) :
    (approxListSum r xs).error ≤
      (xs.map (fun a => a.error)).sum + r.add * xs.length := by
  induction xs with
  | nil => simp [approxListSum, Approx.exact]
  | cons a as ih =>
      simp [approxListSum, Approx.add, Nat.add_assoc, Nat.mul_succ]
      omega

/-- Lift a pointwise closeness hypothesis through `List.map`. -/
theorem pointwiseClose_map {α : Type} (f : α → Approx) (g : α → Int)
    (xs : List α)
    (h : ∀ I, I ∈ xs → (f I).CloseTo (g I)) :
    PointwiseClose (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact PointwiseClose.nil
  | cons I rest ih =>
      exact PointwiseClose.cons (h I (by simp))
        (ih (fun J hJ => h J (by simp [hJ])))

/-- Chain theorem for approximate interval sums.  Each winner interval supplies
one approximate value and one declared error; the middle-term error budget is
the list-sum allowance, and `PayloadContraction.chain_intervalSum` identifies
the exact target with the full-interval sum. -/
theorem chain_intervalSum_close
    (x : Nat → Int) (f : Interval → Approx) (r : RoundingBudget)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (h : ∀ I, I ∈ segments →
      (f I).CloseTo (PayloadContraction.intervalSum x I.lo I.hi)) :
    (approxListSum r (segments.map f)).CloseTo
      (PayloadContraction.intervalSum x lo hi) := by
  have hpoint : PointwiseClose (segments.map f)
      (segments.map (fun I => PayloadContraction.intervalSum x I.lo I.hi)) :=
    pointwiseClose_map f
      (fun I => PayloadContraction.intervalSum x I.lo I.hi) segments h
  have hsum := approxListSum_close r hpoint
  rw [PayloadContraction.chain_intervalSum x hchain] at hsum
  exact hsum

/-- Numeric form of the chain error budget. -/
theorem chain_intervalSum_error_bound
    (f : Interval → Approx) (r : RoundingBudget) (segments : List Interval) :
    (approxListSum r (segments.map f)).error ≤
      ((segments.map f).map (fun a => a.error)).sum +
        r.add * segments.length := by
  simpa using approxListSum_error_bound r (segments.map f)

/-! ## Prefix sums and prefix differences -/

/-- Approximate exclusive prefix sum. -/
def approxPrefixSum (f : Nat → Approx) (r : RoundingBudget) : Nat → Approx
  | 0 => Approx.exact 0
  | n + 1 => (approxPrefixSum f r n).add (f n) r

/-- The value component of an approximate prefix sum is the exact prefix sum of
the approximate values. -/
theorem approxPrefixSum_value_eq (f : Nat → Approx) (r : RoundingBudget) (n : Nat) :
    (approxPrefixSum f r n).value =
      prefixSum (fun k => (f k).value) n := by
  induction n with
  | zero => simp [approxPrefixSum, Approx.exact, prefixSum]
  | succ n ih => simp [approxPrefixSum, Approx.add, ih, prefixSum_succ]

/-- Error propagation for an approximate prefix sum. -/
theorem approxPrefixSum_close (f : Nat → Approx) (x : Nat → Int)
    (r : RoundingBudget) (n : Nat)
    (h : ∀ k, k < n → (f k).CloseTo (x k)) :
    (approxPrefixSum f r n).CloseTo (prefixSum x n) := by
  induction n with
  | zero =>
      simpa [approxPrefixSum, prefixSum] using Approx.exact_close 0
  | succ n ih =>
      have hprev : ∀ k, k < n → (f k).CloseTo (x k) := by
        intro k hk
        exact h k (by omega)
      have hlast : (f n).CloseTo (x n) := h n (by omega)
      simpa [approxPrefixSum, prefixSum_succ] using
        add_close (approxPrefixSum f r n) (f n) (prefixSum x n) (x n) r
          (ih hprev) hlast

/-- Explicit error budget for an approximate prefix sum. -/
theorem approxPrefixSum_error_bound (f : Nat → Approx) (r : RoundingBudget) (n : Nat) :
    (approxPrefixSum f r n).error ≤
      natIntervalSum (fun k => (f k).error) 0 n + r.add * n := by
  induction n with
  | zero => simp [approxPrefixSum, Approx.exact]
  | succ n ih =>
      simp [approxPrefixSum, Approx.add, natIntervalSum_succ,
        Nat.add_assoc, Nat.mul_succ]
      omega

/-- Prefix difference as an approximate subtraction. -/
def approxPrefixDifference (a b : Approx) (r : RoundingBudget) : Approx :=
  a.sub b r

/-- Error propagation for a prefix difference. -/
theorem approxPrefixDifference_close (a b : Approx) (x y : Int)
    (r : RoundingBudget) (ha : a.CloseTo x) (hb : b.CloseTo y) :
    (approxPrefixDifference a b r).CloseTo (x - y) := by
  exact sub_close a b x y r ha hb


/-! ## Payload dots and contractions -/

/-- Approximate inclusive payload dot product.  The gradient is treated as an
exact integer coefficient; the payload carries the declared error. -/
def approxIntervalDot (grad : Nat → Int) (payload : Nat → Approx)
    (r : RoundingBudget) (lo hi : Nat) : Approx :=
  approxIntervalSum (fun t => (payload t).mulConst (grad t) r) r lo hi

/-- The explicit error component of an approximate interval dot. -/
theorem approxIntervalDot_error_eq (grad : Nat → Int) (payload : Nat → Approx)
    (r : RoundingBudget) (lo hi : Nat) :
    (approxIntervalDot grad payload r lo hi).error =
      natIntervalSum
          (fun t => (grad t).natAbs * (payload t).error + r.mul)
          lo (intervalLength lo hi)
        + r.add * intervalLength lo hi := rfl

/-- Error propagation for an inclusive payload dot product. -/
theorem approxIntervalDot_close (grad : Nat → Int) (payload : Nat → Approx)
    (x : Nat → Int) (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (h : ∀ t, lo ≤ t → t ≤ hi → (payload t).CloseTo (x t)) :
    (approxIntervalDot grad payload r lo hi).CloseTo
      (PayloadContraction.intervalDot grad x lo hi) := by
  simpa [approxIntervalDot, PayloadContraction.intervalDot] using
    approxIntervalSum_close (fun t => (payload t).mulConst (grad t) r)
      (fun t => grad t * x t) r lo hi hle
      (fun t htlo hthi =>
        mulConst_close (payload t) (x t) (grad t) r (h t htlo hthi))

/-- Approximate pointwise payload contraction. -/
def approxContraction (grad : Nat → Int) (base candidate : Nat → Approx)
    (r : RoundingBudget) (lo hi : Nat) : Approx :=
  approxIntervalDot grad (fun t => (candidate t).sub (base t) r) r lo hi

/-- The explicit error component of an approximate contraction. -/
theorem approxContraction_error_eq (grad : Nat → Int) (base candidate : Nat → Approx)
    (r : RoundingBudget) (lo hi : Nat) :
    (approxContraction grad base candidate r lo hi).error =
      natIntervalSum
          (fun t => (grad t).natAbs *
            ((candidate t).error + (base t).error + r.sub) + r.mul)
          lo (intervalLength lo hi)
        + r.add * intervalLength lo hi := rfl

/-- Error propagation for the pointwise payload contraction. -/
theorem approxContraction_close (grad : Nat → Int)
    (base candidate : Nat → Approx) (xBase xCandidate : Nat → Int)
    (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (hbase : ∀ t, lo ≤ t → t ≤ hi → (base t).CloseTo (xBase t))
    (hcand : ∀ t, lo ≤ t → t ≤ hi → (candidate t).CloseTo (xCandidate t)) :
    (approxContraction grad base candidate r lo hi).CloseTo
      (PayloadContraction.contraction grad xBase xCandidate lo hi) := by
  simpa [approxContraction, PayloadContraction.contraction] using
    approxIntervalDot_close grad
      (fun t => (candidate t).sub (base t) r)
      (fun t => xCandidate t - xBase t) r lo hi hle
      (fun t htlo hthi =>
        sub_close (candidate t) (base t) (xCandidate t) (xBase t) r
          (hcand t htlo hthi) (hbase t htlo hthi))

/-! ## Constant and shifted endpoints -/

/-- Approximate constant-endpoint contraction.  The gradient interval sum is
treated as exact; `r.mul` accounts for the multiplication by the constant
payload value, and the baseline dot carries its own rounding and input error. -/
def approxConstantEndpointContraction (grad : Nat → Int) (base : Nat → Approx)
    (c : Int) (r : RoundingBudget) (lo hi : Nat) : Approx :=
  ((Approx.exact (intervalSum grad lo hi)).mulConst c r).sub
    (approxIntervalDot grad base r lo hi) r

/-- Error propagation for a constant-endpoint contraction. -/
theorem approxConstantEndpointContraction_close (grad : Nat → Int)
    (base : Nat → Approx) (x : Nat → Int) (c : Int)
    (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (hbase : ∀ t, lo ≤ t → t ≤ hi → (base t).CloseTo (x t)) :
    (approxConstantEndpointContraction grad base c r lo hi).CloseTo
      (PayloadContraction.constantEndpointContraction grad x c lo hi) := by
  have hmul := mulConst_close (Approx.exact (intervalSum grad lo hi))
    (intervalSum grad lo hi) c r (Approx.exact_close _)
  have hdot := approxIntervalDot_close grad base x r lo hi hle hbase
  simpa [approxConstantEndpointContraction,
    PayloadContraction.constantEndpointContraction] using
    sub_close ((Approx.exact (intervalSum grad lo hi)).mulConst c r)
      (approxIntervalDot grad base r lo hi)
      (c * intervalSum grad lo hi) (PayloadContraction.intervalDot grad x lo hi)
      r hmul hdot

/-- Explicit upper bound for the constant-endpoint contraction error. -/
theorem approxConstantEndpointContraction_error_le (grad : Nat → Int)
    (base : Nat → Approx) (c : Int) (r : RoundingBudget) (lo hi : Nat) :
    (approxConstantEndpointContraction grad base c r lo hi).error ≤
      (approxIntervalDot grad base r lo hi).error + r.mul + r.sub := by
  simp [approxConstantEndpointContraction, Approx.sub, Approx.mulConst,
    Approx.exact]
  omega

/-- Totalized approximate shifted payload read, mirroring
`PayloadContraction.shiftedPayload`. -/
def approxShiftedPayload (payload : Nat → Approx) (shift : Int) (t : Nat) : Approx :=
  if _ : 0 ≤ (t : Int) + shift then
    payload (Int.toNat ((t : Int) + shift))
  else
    Approx.exact 0

/-- Pointwise error propagation for a shifted payload read. -/
theorem approxShiftedPayload_close (payload : Nat → Approx) (x : Nat → Int)
    (shift : Int) (h : ∀ k, (payload k).CloseTo (x k)) (t : Nat) :
    (approxShiftedPayload payload shift t).CloseTo
      (PayloadContraction.shiftedPayload x shift t) := by
  by_cases hnonneg : 0 ≤ (t : Int) + shift
  · simpa [approxShiftedPayload, PayloadContraction.shiftedPayload, hnonneg] using
      h (Int.toNat ((t : Int) + shift))
  · simpa [approxShiftedPayload, PayloadContraction.shiftedPayload, hnonneg] using
      Approx.exact_close 0

/-- Approximate shifted interval dot. -/
def approxShiftedIntervalDot (grad : Nat → Int) (payload : Nat → Approx)
    (shift : Int) (r : RoundingBudget) (lo hi : Nat) : Approx :=
  approxIntervalDot grad (fun t => approxShiftedPayload payload shift t) r lo hi

/-- Error propagation for a shifted interval dot. -/
theorem approxShiftedIntervalDot_close (grad : Nat → Int) (payload : Nat → Approx)
    (x : Nat → Int) (shift : Int) (r : RoundingBudget) (lo hi : Nat)
    (hle : lo ≤ hi) (h : ∀ k, (payload k).CloseTo (x k)) :
    (approxShiftedIntervalDot grad payload shift r lo hi).CloseTo
      (PayloadContraction.shiftedIntervalDot grad x shift lo hi) := by
  change (approxIntervalDot grad
      (fun t => approxShiftedPayload payload shift t) r lo hi).CloseTo
    (intervalSum (fun t => grad t * PayloadContraction.shiftedPayload x shift t)
      lo hi)
  exact approxIntervalDot_close grad (fun t => approxShiftedPayload payload shift t)
    (fun t => PayloadContraction.shiftedPayload x shift t) r lo hi hle
    (fun t _ _ => approxShiftedPayload_close payload x shift h t)

/-- Approximate endpoint-shift contraction. -/
def approxEndpointShiftContraction (grad : Nat → Int)
    (base payload : Nat → Approx) (endpointShift : Int)
    (r : RoundingBudget) (lo hi : Nat) : Approx :=
  (approxShiftedIntervalDot grad payload (endpointShift + 1) r lo hi).sub
    (approxIntervalDot grad base r lo hi) r

/-- Error propagation for an endpoint-shift contraction. -/
theorem approxEndpointShiftContraction_close (grad : Nat → Int)
    (base payload : Nat → Approx) (xBase xPayload : Nat → Int)
    (endpointShift : Int) (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (hbase : ∀ t, lo ≤ t → t ≤ hi → (base t).CloseTo (xBase t))
    (hpayload : ∀ t, (payload t).CloseTo (xPayload t)) :
    (approxEndpointShiftContraction grad base payload endpointShift r lo hi).CloseTo
      (PayloadContraction.endpointShiftContraction grad xBase xPayload endpointShift
        lo hi) := by
  have hshift := approxShiftedIntervalDot_close grad payload xPayload
    (endpointShift + 1) r lo hi hle hpayload
  have hbaseDot := approxIntervalDot_close grad base xBase r lo hi hle hbase
  simpa [approxEndpointShiftContraction,
    PayloadContraction.endpointShiftContraction, PayloadContraction.shiftedContraction]
    using sub_close
      (approxShiftedIntervalDot grad payload (endpointShift + 1) r lo hi)
      (approxIntervalDot grad base r lo hi)
      (PayloadContraction.shiftedIntervalDot grad xPayload (endpointShift + 1) lo hi)
      (PayloadContraction.intervalDot grad xBase lo hi) r hshift hbaseDot

/-- Explicit upper bound for the endpoint-shift contraction error. -/
theorem approxEndpointShiftContraction_error_le (grad : Nat → Int)
    (base payload : Nat → Approx) (endpointShift : Int)
    (r : RoundingBudget) (lo hi : Nat) :
    (approxEndpointShiftContraction grad base payload endpointShift r lo hi).error ≤
      (approxShiftedIntervalDot grad payload (endpointShift + 1) r lo hi).error +
        (approxIntervalDot grad base r lo hi).error + r.sub := by
  simp [approxEndpointShiftContraction, Approx.sub]


/-- Generic per-segment chain propagation: if every interval carries an
approximate value close to its own exact segment value, then the accumulated
list is close to the exact segment sum. -/
theorem chain_segment_close
    (f : Interval → Approx) (g : Interval → Int) (r : RoundingBudget)
    (segments : List Interval)
    (h : ∀ I, I ∈ segments → (f I).CloseTo (g I)) :
    (approxListSum r (segments.map f)).CloseTo (segments.map g).sum :=
  approxListSum_close r (pointwiseClose_map f g segments h)

/-- Chain-error theorem for pointwise contractions.  The hypotheses are global
pointwise error bounds on the two payload tracks; each winner interval then
contributes the corresponding interval contraction. -/
theorem chain_contraction_close (grad : Nat → Int)
    (base candidate : Nat → Approx) (xBase xCandidate : Nat → Int)
    (r : RoundingBudget)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hbase : ∀ t, (base t).CloseTo (xBase t))
    (hcand : ∀ t, (candidate t).CloseTo (xCandidate t)) :
    (approxListSum r
      (segments.map (fun I =>
        approxContraction grad base candidate r I.lo I.hi))).CloseTo
      (PayloadContraction.contraction grad xBase xCandidate lo hi) := by
  have h := chain_segment_close
    (fun I => approxContraction grad base candidate r I.lo I.hi)
    (fun I => PayloadContraction.contraction grad xBase xCandidate I.lo I.hi)
    r segments (fun I _ =>
      approxContraction_close grad base candidate xBase xCandidate r
        I.lo I.hi I.nonempty (fun t _ _ => hbase t) (fun t _ _ => hcand t))
  rw [PayloadContraction.chain_contraction grad xBase xCandidate hchain] at h
  exact h

/-- Chain-error theorem for constant-endpoint contractions. -/
theorem chain_constantEndpointContraction_close (grad : Nat → Int)
    (base : Nat → Approx) (x : Nat → Int) (c : Int) (r : RoundingBudget)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hbase : ∀ t, (base t).CloseTo (x t)) :
    (approxListSum r
      (segments.map (fun I =>
        approxConstantEndpointContraction grad base c r I.lo I.hi))).CloseTo
      (PayloadContraction.constantEndpointContraction grad x c lo hi) := by
  have h := chain_segment_close
    (fun I => approxConstantEndpointContraction grad base c r I.lo I.hi)
    (fun I => PayloadContraction.constantEndpointContraction grad x c I.lo I.hi)
    r segments (fun I _ =>
      approxConstantEndpointContraction_close grad base x c r I.lo I.hi
        I.nonempty (fun t _ _ => hbase t))
  rw [PayloadContraction.chain_constantEndpointContraction grad x c hchain] at h
  exact h

/-- Chain-error theorem for shifted endpoint contractions.  The shifted read
can leave the current interval, so the payload error hypothesis is global. -/
theorem chain_endpointShiftContraction_close (grad : Nat → Int)
    (base payload : Nat → Approx) (xBase xPayload : Nat → Int)
    (endpointShift : Int) (r : RoundingBudget)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hbase : ∀ t, (base t).CloseTo (xBase t))
    (hpayload : ∀ t, (payload t).CloseTo (xPayload t)) :
    (approxListSum r
      (segments.map (fun I =>
        approxEndpointShiftContraction grad base payload endpointShift r I.lo I.hi))).CloseTo
      (PayloadContraction.endpointShiftContraction grad xBase xPayload endpointShift
        lo hi) := by
  have h := chain_segment_close
    (fun I => approxEndpointShiftContraction grad base payload endpointShift r I.lo I.hi)
    (fun I => PayloadContraction.endpointShiftContraction grad xBase xPayload
      endpointShift I.lo I.hi)
    r segments (fun I _ =>
      approxEndpointShiftContraction_close grad base payload xBase xPayload
        endpointShift r I.lo I.hi I.nonempty
        (fun t _ _ => hbase t) hpayload)
  rw [PayloadContraction.chain_endpointShiftContraction grad xBase xPayload
    endpointShift hchain] at h
  exact h


/-! ## Exact degeneration at zero budget -/

/-- A zero-error approximation that is close to an exact value has equal value
component. -/
theorem value_eq_of_closeTo_zero_error (a : Approx) (x : Int)
    (h : a.CloseTo x) (hzero : a.error = 0) :
    a.value = x := by
  have hle : Int.natAbs (a.value - x) ≤ 0 := by
    simpa [Approx.CloseTo, hzero] using h
  have hz : Int.natAbs (a.value - x) = 0 := Nat.eq_zero_of_le_zero hle
  exact Int.eq_of_sub_eq_zero (Int.natAbs_eq_zero.mp hz)

/-- If the value components are already exact on an interval, then the
approximate interval sum has the exact integer interval sum as value.  The
rounding budget does not affect the value component. -/
theorem approxIntervalSum_value_eq_of_pointwise
    (f : Nat → Approx) (x : Nat → Int) (r : RoundingBudget)
    (lo hi : Nat) (hle : lo ≤ hi)
    (h : ∀ t, lo ≤ t → t ≤ hi → (f t).value = x t) :
    (approxIntervalSum f r lo hi).value = intervalSum x lo hi := by
  unfold approxIntervalSum
  apply intervalSum_congr_on _ _ lo hi hle
  intro t htlo hthi
  exact h t htlo hthi

/-- Exact-value degeneration for an approximate interval dot. -/
theorem approxIntervalDot_value_eq_of_pointwise
    (grad : Nat → Int) (payload : Nat → Approx) (x : Nat → Int)
    (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (h : ∀ t, lo ≤ t → t ≤ hi → (payload t).value = x t) :
    (approxIntervalDot grad payload r lo hi).value =
      PayloadContraction.intervalDot grad x lo hi := by
  unfold approxIntervalDot approxIntervalSum
  rw [PayloadContraction.intervalDot]
  apply intervalSum_congr_on _ _ lo hi hle
  intro t htlo hthi
  simp [Approx.mulConst, h t htlo hthi]

/-- Exact-value degeneration for an approximate pointwise contraction. -/
theorem approxContraction_value_eq_of_pointwise
    (grad : Nat → Int) (base candidate : Nat → Approx)
    (xBase xCandidate : Nat → Int) (r : RoundingBudget)
    (lo hi : Nat) (hle : lo ≤ hi)
    (hbase : ∀ t, lo ≤ t → t ≤ hi → (base t).value = xBase t)
    (hcand : ∀ t, lo ≤ t → t ≤ hi → (candidate t).value = xCandidate t) :
    (approxContraction grad base candidate r lo hi).value =
      PayloadContraction.contraction grad xBase xCandidate lo hi := by
  unfold approxContraction approxIntervalDot approxIntervalSum
  rw [PayloadContraction.contraction, PayloadContraction.intervalDot]
  apply intervalSum_congr_on _ _ lo hi hle
  intro t htlo hthi
  simp [Approx.mulConst, Approx.sub, hcand t htlo hthi, hbase t htlo hthi]

/-- Exact-value degeneration for a constant-endpoint contraction. -/
theorem approxConstantEndpointContraction_value_eq_of_pointwise
    (grad : Nat → Int) (base : Nat → Approx) (x : Nat → Int)
    (c : Int) (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (hbase : ∀ t, lo ≤ t → t ≤ hi → (base t).value = x t) :
    (approxConstantEndpointContraction grad base c r lo hi).value =
      PayloadContraction.constantEndpointContraction grad x c lo hi := by
  simp [approxConstantEndpointContraction, Approx.sub, Approx.mulConst,
    Approx.exact,
    approxIntervalDot_value_eq_of_pointwise grad base x r lo hi hle hbase,
    PayloadContraction.constantEndpointContraction]

/-- Exact-value degeneration for a totalized shifted payload read. -/
theorem approxShiftedPayload_value_eq_of_pointwise
    (payload : Nat → Approx) (x : Nat → Int) (shift : Int)
    (h : ∀ k, (payload k).value = x k) (t : Nat) :
    (approxShiftedPayload payload shift t).value =
      PayloadContraction.shiftedPayload x shift t := by
  by_cases hnonneg : 0 ≤ (t : Int) + shift
  · simpa [approxShiftedPayload, PayloadContraction.shiftedPayload, hnonneg] using
      h (Int.toNat ((t : Int) + shift))
  · simp [approxShiftedPayload, PayloadContraction.shiftedPayload, hnonneg,
      Approx.exact]

/-- Exact-value degeneration for an approximate shifted interval dot. -/
theorem approxShiftedIntervalDot_value_eq_of_pointwise
    (grad : Nat → Int) (payload : Nat → Approx) (x : Nat → Int)
    (shift : Int) (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (h : ∀ k, (payload k).value = x k) :
    (approxShiftedIntervalDot grad payload shift r lo hi).value =
      PayloadContraction.shiftedIntervalDot grad x shift lo hi := by
  change (approxIntervalDot grad
      (fun t => approxShiftedPayload payload shift t) r lo hi).value =
    intervalSum (fun t => grad t * PayloadContraction.shiftedPayload x shift t)
      lo hi
  rw [approxIntervalDot_value_eq_of_pointwise grad
    (fun t => approxShiftedPayload payload shift t)
    (fun t => PayloadContraction.shiftedPayload x shift t) r lo hi hle]
  · rfl
  · intro t _ _
    exact approxShiftedPayload_value_eq_of_pointwise payload x shift h t

/-- Exact-value degeneration for an approximate endpoint-shift contraction. -/
theorem approxEndpointShiftContraction_value_eq_of_pointwise
    (grad : Nat → Int) (base payload : Nat → Approx)
    (xBase xPayload : Nat → Int) (endpointShift : Int)
    (r : RoundingBudget) (lo hi : Nat) (hle : lo ≤ hi)
    (hbase : ∀ t, lo ≤ t → t ≤ hi → (base t).value = xBase t)
    (hpayload : ∀ k, (payload k).value = xPayload k) :
    (approxEndpointShiftContraction grad base payload endpointShift r lo hi).value =
      PayloadContraction.endpointShiftContraction grad xBase xPayload endpointShift
        lo hi := by
  simp [approxEndpointShiftContraction, Approx.sub,
    approxShiftedIntervalDot_value_eq_of_pointwise grad payload xPayload
      (endpointShift + 1) r lo hi hle hpayload,
    approxIntervalDot_value_eq_of_pointwise grad base xBase r lo hi hle hbase,
    PayloadContraction.endpointShiftContraction, PayloadContraction.shiftedContraction]

/-- Exact segment-value degeneration for an accumulated approximation. -/
theorem chain_exact_of_segment_values
    (f : Interval → Approx) (g : Interval → Int) (r : RoundingBudget)
    (segments : List Interval)
    (hvalue : ∀ I, I ∈ segments → (f I).value = g I) :
    (approxListSum r (segments.map f)).value = (segments.map g).sum := by
  rw [approxListSum_value_eq, List.map_map]
  change (segments.map (fun I => (f I).value)).sum = (segments.map g).sum
  have hmap : (segments.map (fun I => (f I).value)) = segments.map g := by
    apply List.map_congr_left
    intro I hI
    exact hvalue I hI
  rw [hmap]

/-- Zero-budget chain degeneration to the exact interval-sum theorem. -/
theorem chain_intervalSum_exact_of_values
    (x : Nat → Int) (f : Interval → Approx)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hvalue : ∀ I, I ∈ segments →
      (f I).value = PayloadContraction.intervalSum x I.lo I.hi) :
    (approxListSum RoundingBudget.zero (segments.map f)).value =
      PayloadContraction.intervalSum x lo hi := by
  rw [chain_exact_of_segment_values f
    (fun I => PayloadContraction.intervalSum x I.lo I.hi) RoundingBudget.zero
    segments hvalue]
  exact PayloadContraction.chain_intervalSum x hchain

/-- Zero-budget chain degeneration to the exact contraction theorem. -/
theorem chain_contraction_exact_of_values (grad : Nat → Int)
    (base candidate : Nat → Approx) (xBase xCandidate : Nat → Int)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hvalue : ∀ I, I ∈ segments →
      (approxContraction grad base candidate RoundingBudget.zero I.lo I.hi).value =
        PayloadContraction.contraction grad xBase xCandidate I.lo I.hi) :
    (approxListSum RoundingBudget.zero
      (segments.map (fun I =>
        approxContraction grad base candidate RoundingBudget.zero
          I.lo I.hi))).value =
      PayloadContraction.contraction grad xBase xCandidate lo hi := by
  rw [chain_exact_of_segment_values
    (fun I => approxContraction grad base candidate RoundingBudget.zero I.lo I.hi)
    (fun I => PayloadContraction.contraction grad xBase xCandidate I.lo I.hi)
    RoundingBudget.zero segments hvalue]
  exact PayloadContraction.chain_contraction grad xBase xCandidate hchain

/-- Zero-budget chain degeneration to the exact constant-endpoint theorem. -/
theorem chain_constantEndpointContraction_exact_of_values (grad : Nat → Int)
    (base : Nat → Approx) (x : Nat → Int) (c : Int)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hvalue : ∀ I, I ∈ segments →
      (approxConstantEndpointContraction grad base c RoundingBudget.zero
        I.lo I.hi).value =
        PayloadContraction.constantEndpointContraction grad x c I.lo I.hi) :
    (approxListSum RoundingBudget.zero
      (segments.map (fun I =>
        approxConstantEndpointContraction grad base c RoundingBudget.zero
          I.lo I.hi))).value =
      PayloadContraction.constantEndpointContraction grad x c lo hi := by
  rw [chain_exact_of_segment_values
    (fun I => approxConstantEndpointContraction grad base c RoundingBudget.zero
      I.lo I.hi)
    (fun I => PayloadContraction.constantEndpointContraction grad x c I.lo I.hi)
    RoundingBudget.zero segments hvalue]
  exact PayloadContraction.chain_constantEndpointContraction grad x c hchain

/-- Zero-budget chain degeneration to the exact shifted-endpoint theorem. -/
theorem chain_endpointShiftContraction_exact_of_values (grad : Nat → Int)
    (base payload : Nat → Approx) (xBase xPayload : Nat → Int)
    (endpointShift : Int)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hvalue : ∀ I, I ∈ segments →
      (approxEndpointShiftContraction grad base payload endpointShift
        RoundingBudget.zero I.lo I.hi).value =
        PayloadContraction.endpointShiftContraction grad xBase xPayload endpointShift
          I.lo I.hi) :
    (approxListSum RoundingBudget.zero
      (segments.map (fun I =>
        approxEndpointShiftContraction grad base payload endpointShift
          RoundingBudget.zero I.lo I.hi))).value =
      PayloadContraction.endpointShiftContraction grad xBase xPayload endpointShift
        lo hi := by
  rw [chain_exact_of_segment_values
    (fun I => approxEndpointShiftContraction grad base payload endpointShift
      RoundingBudget.zero I.lo I.hi)
    (fun I => PayloadContraction.endpointShiftContraction grad xBase xPayload
      endpointShift I.lo I.hi)
    RoundingBudget.zero segments hvalue]
  exact PayloadContraction.chain_endpointShiftContraction grad xBase xPayload
    endpointShift hchain


/-- Direct zero-budget degeneration of a contraction chain: exact value
components and zero rounding recover `PayloadContraction.chain_contraction`. -/
theorem chain_contraction_exact (grad : Nat → Int)
    (base candidate : Nat → Approx) (xBase xCandidate : Nat → Int)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hbase : ∀ t, (base t).value = xBase t)
    (hcand : ∀ t, (candidate t).value = xCandidate t) :
    (approxListSum RoundingBudget.zero
      (segments.map (fun I =>
        approxContraction grad base candidate RoundingBudget.zero
          I.lo I.hi))).value =
      PayloadContraction.contraction grad xBase xCandidate lo hi := by
  apply chain_contraction_exact_of_values grad base candidate xBase xCandidate hchain
  intro I _
  exact approxContraction_value_eq_of_pointwise grad base candidate xBase xCandidate
    RoundingBudget.zero I.lo I.hi I.nonempty
    (fun t _ _ => hbase t) (fun t _ _ => hcand t)

/-- Direct zero-budget degeneration of a constant-endpoint chain. -/
theorem chain_constantEndpointContraction_exact (grad : Nat → Int)
    (base : Nat → Approx) (x : Nat → Int) (c : Int)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hbase : ∀ t, (base t).value = x t) :
    (approxListSum RoundingBudget.zero
      (segments.map (fun I =>
        approxConstantEndpointContraction grad base c RoundingBudget.zero
          I.lo I.hi))).value =
      PayloadContraction.constantEndpointContraction grad x c lo hi := by
  apply chain_constantEndpointContraction_exact_of_values grad base x c hchain
  intro I _
  exact approxConstantEndpointContraction_value_eq_of_pointwise grad base x c
    RoundingBudget.zero I.lo I.hi I.nonempty (fun t _ _ => hbase t)

/-- Direct zero-budget degeneration of a shifted-endpoint chain. -/
theorem chain_endpointShiftContraction_exact (grad : Nat → Int)
    (base payload : Nat → Approx) (xBase xPayload : Nat → Int)
    (endpointShift : Int)
    {lo hi : Nat} {segments : List Interval}
    (hchain : ChainFromTo lo hi segments)
    (hbase : ∀ t, (base t).value = xBase t)
    (hpayload : ∀ t, (payload t).value = xPayload t) :
    (approxListSum RoundingBudget.zero
      (segments.map (fun I =>
        approxEndpointShiftContraction grad base payload endpointShift
          RoundingBudget.zero I.lo I.hi))).value =
      PayloadContraction.endpointShiftContraction grad xBase xPayload endpointShift
        lo hi := by
  apply chain_endpointShiftContraction_exact_of_values grad base payload xBase xPayload
    endpointShift hchain
  intro I _
  exact approxEndpointShiftContraction_value_eq_of_pointwise grad base payload
    xBase xPayload endpointShift RoundingBudget.zero I.lo I.hi I.nonempty
    (fun t _ _ => hbase t) hpayload

end PayloadErrorBound

import Std

/-!
## M4 payload / credit contraction algebra

This is the route-independent arithmetic layer of the M4 contraction described
in `rosa_streaming/CORE_PLAN.md` and notes §§1.4/11.3/18.  It deliberately
does not import `Route`, `RosBridge`, or an M3 envelope module: M3 supplies
winner intervals, and this file proves that their contractions telescope.

The proof domain is `Int`.  This is exact for integer route indices and for an
integer model of payload coordinates.  The definitions use one scalar
coordinate; the D-dimensional runtime dot product is contracted componentwise,
so the same algebra applies coordinate by coordinate.  Runtime uses
`Float32`/`Float64` dot products, so these theorems do **not** claim bitwise
equality with a runtime reduction: float addition is not associative and a
different summation order may round differently.  The runtime bridge must
separately preserve/evaluate the intended reduction and bound or measure its
floating-point error.

Intervals are inclusive, `[lo, hi]`, matching the runtime
`RepairTrackTerm`.  Prefixes are exclusive:
`prefixSum w n = sum_{0 <= t < n} w[t]`.
-/

namespace PayloadContraction

/-! ## Prefix sums and interval sums -/

/-- Exclusive prefix sum of a scalar sequence. -/
def prefixSum (w : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => prefixSum w n + w n

@[simp] theorem prefixSum_zero (w : Nat → Int) : prefixSum w 0 = 0 := rfl

@[simp] theorem prefixSum_succ (w : Nat → Int) (n : Nat) :
    prefixSum w (n + 1) = prefixSum w n + w n := rfl

/-- Inclusive interval sum as a prefix difference. -/
def intervalSum (w : Nat → Int) (lo hi : Nat) : Int :=
  prefixSum w (hi + 1) - prefixSum w lo

/-- The defining prefix-difference identity for an interval sum. -/
theorem intervalSum_eq_prefix_sub (w : Nat → Int) (lo hi : Nat) :
    intervalSum w lo hi = prefixSum w (hi + 1) - prefixSum w lo := rfl

/-- A one-point interval is exactly the point value. -/
theorem intervalSum_singleton (w : Nat → Int) (lo : Nat) :
    intervalSum w lo lo = w lo := by
  simp [intervalSum, prefixSum]
  omega

/-- Inclusive interval concatenation: `[lo, mid]` followed by
`[mid+1, hi]` is `[lo, hi]`. -/
theorem intervalSum_concat (w : Nat → Int) (lo mid hi : Nat) :
    intervalSum w lo mid + intervalSum w (mid + 1) hi =
      intervalSum w lo hi := by
  unfold intervalSum
  omega

/-- Prefix sums are additive in their sequence argument. -/
theorem prefixSum_add (w₁ w₂ : Nat → Int) (n : Nat) :
    prefixSum (fun t => w₁ t + w₂ t) n = prefixSum w₁ n + prefixSum w₂ n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
      simp only [prefixSum_succ, ih]
      omega

/-- Prefix sums commute with subtraction of sequences. -/
theorem prefixSum_sub (w₁ w₂ : Nat → Int) (n : Nat) :
    prefixSum (fun t => w₁ t - w₂ t) n = prefixSum w₁ n - prefixSum w₂ n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
      simp only [prefixSum_succ, ih]
      omega

/-- Prefix sums commute with a scalar multiple on the left. -/
theorem prefixSum_mul_left (a : Int) (w : Nat → Int) (n : Nat) :
    prefixSum (fun t => a * w t) n = a * prefixSum w n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
      simp only [prefixSum_succ, ih]
      rw [Int.mul_add]

/-- Prefix sums commute with a scalar multiple on the right. -/
theorem prefixSum_mul_right (w : Nat → Int) (a : Int) (n : Nat) :
    prefixSum (fun t => w t * a) n = prefixSum w n * a := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
      simp only [prefixSum_succ, ih]
      rw [Int.add_mul]

/-- Interval sums are additive. -/
theorem intervalSum_add (w₁ w₂ : Nat → Int) (lo hi : Nat) :
    intervalSum (fun t => w₁ t + w₂ t) lo hi =
      intervalSum w₁ lo hi + intervalSum w₂ lo hi := by
  unfold intervalSum
  rw [prefixSum_add, prefixSum_add]
  omega

/-- Interval sums commute with sequence subtraction. -/
theorem intervalSum_sub (w₁ w₂ : Nat → Int) (lo hi : Nat) :
    intervalSum (fun t => w₁ t - w₂ t) lo hi =
      intervalSum w₁ lo hi - intervalSum w₂ lo hi := by
  unfold intervalSum
  rw [prefixSum_sub, prefixSum_sub]
  omega

/-- Interval sums commute with a scalar multiple on the left. -/
theorem intervalSum_mul_left (a : Int) (w : Nat → Int) (lo hi : Nat) :
    intervalSum (fun t => a * w t) lo hi = a * intervalSum w lo hi := by
  unfold intervalSum
  rw [prefixSum_mul_left, prefixSum_mul_left]
  rw [Int.mul_sub]

/-- Interval sums commute with a scalar multiple on the right. -/
theorem intervalSum_mul_right (w : Nat → Int) (a : Int) (lo hi : Nat) :
    intervalSum (fun t => w t * a) lo hi = intervalSum w lo hi * a := by
  unfold intervalSum
  rw [prefixSum_mul_right, prefixSum_mul_right]
  rw [Int.sub_mul]

/-- If two sequences agree on an inclusive interval, their interval sums agree.
This is the local congruence used to replace a winner interval by its
constant/shifted payload model. -/
theorem intervalSum_congr_on (w₁ w₂ : Nat → Int) (lo hi : Nat)
    (hle : lo ≤ hi)
    (h : ∀ t, lo ≤ t → t ≤ hi → w₁ t = w₂ t) :
    intervalSum w₁ lo hi = intervalSum w₂ lo hi := by
  revert lo
  refine Nat.strongRecOn hi ?_
  intro hi ih lo hle h
  by_cases hlo : lo = hi
  · subst hlo
    rw [intervalSum_singleton, intervalSum_singleton]
    exact h lo (Nat.le_refl lo) (Nat.le_refl lo)
  · have hlt : lo < hi := Nat.lt_of_le_of_ne hle hlo
    have hhi : 0 < hi := Nat.lt_of_le_of_lt (Nat.zero_le lo) hlt
    have hpredlt : hi - 1 < hi := Nat.sub_one_lt (Nat.ne_of_gt hhi)
    have hlepred : lo ≤ hi - 1 := by omega
    rw [← intervalSum_concat w₁ lo (hi - 1) hi,
        ← intervalSum_concat w₂ lo (hi - 1) hi]
    rw [show (hi - 1) + 1 = hi by omega]
    rw [intervalSum_singleton, intervalSum_singleton]
    rw [ih (hi - 1) hpredlt lo hlepred
      (fun t h1 h2 => h t h1 (by omega))]
    rw [h hi (by omega) (Nat.le_refl hi)]

/-! ## Payload dot products and contractions -/

/-- Inclusive interval payload dot product. -/
def intervalDot (grad payload : Nat → Int) (lo hi : Nat) : Int :=
  intervalSum (fun t => grad t * payload t) lo hi

/-- If two payload sequences agree on an interval, their interval dot products
agree there. -/
theorem intervalDot_congr_on (grad payload₁ payload₂ : Nat → Int) (lo hi : Nat)
    (hle : lo ≤ hi)
    (h : ∀ t, lo ≤ t → t ≤ hi → payload₁ t = payload₂ t) :
    intervalDot grad payload₁ lo hi = intervalDot grad payload₂ lo hi := by
  unfold intervalDot
  apply intervalSum_congr_on _ _ lo hi hle
  intro t h1 h2
  rw [h t h1 h2]

/-- Interval payload dots concatenate. -/
theorem intervalDot_concat (grad payload : Nat → Int) (lo mid hi : Nat) :
    intervalDot grad payload lo mid + intervalDot grad payload (mid + 1) hi =
      intervalDot grad payload lo hi := by
  unfold intervalDot
  exact intervalSum_concat (fun t => grad t * payload t) lo mid hi

/-- The interval payload dot is itself a prefix difference. -/
theorem intervalDot_eq_prefix_sub (grad payload : Nat → Int) (lo hi : Nat) :
    intervalDot grad payload lo hi =
      prefixSum (fun t => grad t * payload t) (hi + 1) -
        prefixSum (fun t => grad t * payload t) lo := rfl

/-- The pointwise payload-difference contraction. -/
def contraction (grad base candidate : Nat → Int) (lo hi : Nat) : Int :=
  intervalDot grad (fun t => candidate t - base t) lo hi

/-- The contraction is the difference of candidate and baseline dots. -/
theorem contraction_eq_dot_sub (grad base candidate : Nat → Int) (lo hi : Nat) :
    contraction grad base candidate lo hi =
      intervalDot grad candidate lo hi - intervalDot grad base lo hi := by
  unfold contraction intervalDot
  rw [show (fun t => grad t * (candidate t - base t)) =
      (fun t => grad t * candidate t - grad t * base t) by
    funext t
    rw [Int.mul_sub]]
  exact intervalSum_sub (fun t => grad t * candidate t) (fun t => grad t * base t) lo hi

/-- Dot product with a constant payload factors through the interval grad sum. -/
theorem intervalDot_const (grad : Nat → Int) (c : Int) (lo hi : Nat) :
    intervalDot grad (fun _ => c) lo hi = c * intervalSum grad lo hi := by
  unfold intervalDot
  rw [intervalSum_mul_right]
  rw [Int.mul_comm]

/-- Constant-endpoint contraction: a constant candidate payload contributes
the shared payload value times the interval sum of the gradients. -/
def constantEndpointContraction (grad base : Nat → Int) (c : Int) (lo hi : Nat) : Int :=
  c * intervalSum grad lo hi - intervalDot grad base lo hi

/-- Constant-endpoint contraction is the pointwise-difference contraction with
the constant candidate. -/
theorem constantEndpointContraction_eq_contraction
    (grad base : Nat → Int) (c : Int) (lo hi : Nat) :
    constantEndpointContraction grad base c lo hi =
      contraction grad base (fun _ => c) lo hi := by
  rw [constantEndpointContraction, contraction_eq_dot_sub, intervalDot_const]

/-- Interval concatenation for the constant-endpoint contraction. -/
theorem constantEndpointContraction_concat
    (grad base : Nat → Int) (c : Int) (lo mid hi : Nat) :
    constantEndpointContraction grad base c lo mid +
      constantEndpointContraction grad base c (mid + 1) hi =
        constantEndpointContraction grad base c lo hi := by
  unfold constantEndpointContraction
  have hs := intervalSum_concat grad lo mid hi
  have hb := intervalDot_concat grad base lo mid hi
  rw [← hs, ← hb, Int.mul_add]
  omega

/-! ## Shifted payloads (`endpoint = t + shift`) -/

/-- Totalized shifted payload read.  Here `shift` is the **payload-index**
shift: on the valid domain `0 <= t + shift` this is `payload[t + shift]`.
If a route endpoint is `e(t) = t + s` and runtime reads `V[e(t)+1]`, use the
endpoint wrapper below with `s`; it passes `s + 1` here.  Outside the valid
domain this totalized definition returns zero, so runtime must keep its
explicit bounds/OOB guard. -/
def shiftedPayload (payload : Nat → Int) (shift : Int) (t : Nat) : Int :=
  if _ : 0 ≤ (t : Int) + shift then
    payload (Int.toNat ((t : Int) + shift))
  else
    0

/-- On the valid domain, the totalized shifted read is the intended read. -/
theorem shiftedPayload_eq_of_nonneg (payload : Nat → Int) (shift : Int) (t : Nat)
    (h : 0 ≤ (t : Int) + shift) :
    shiftedPayload payload shift t =
      payload (Int.toNat ((t : Int) + shift)) := by
  simp [shiftedPayload, h]

/-- The shifted product `grad[t] * payload[t+shift]`. -/
def shiftedProduct (grad payload : Nat → Int) (shift : Int) (t : Nat) : Int :=
  grad t * shiftedPayload payload shift t

/-- Inclusive interval sum of shifted products. -/
def shiftedIntervalDot (grad payload : Nat → Int) (shift : Int) (lo hi : Nat) : Int :=
  intervalSum (shiftedProduct grad payload shift) lo hi

/-- Shifted-product contraction against an arbitrary baseline payload.
`shift` is the payload-index shift, not a route-endpoint shift. -/
def shiftedContraction (grad base payload : Nat → Int) (shift : Int)
    (lo hi : Nat) : Int :=
  shiftedIntervalDot grad payload shift lo hi - intervalDot grad base lo hi

/-- Endpoint-level wrapper for the ROSA read `V[endpoint + 1]`.  If the
endpoint track is `e(t) = t + endpointShift`, this is exactly the intended
shifted contraction. -/
def endpointShiftContraction (grad base payload : Nat → Int)
    (endpointShift : Int) (lo hi : Nat) : Int :=
  shiftedContraction grad base payload (endpointShift + 1) lo hi

/-- Shifted interval dot is the corresponding interval sum. -/
theorem shiftedIntervalDot_eq_intervalSum
    (grad payload : Nat → Int) (shift : Int) (lo hi : Nat) :
    shiftedIntervalDot grad payload shift lo hi =
      intervalSum (shiftedProduct grad payload shift) lo hi := rfl

/-- Shifted interval dots concatenate. -/
theorem shiftedIntervalDot_concat
    (grad payload : Nat → Int) (shift : Int) (lo mid hi : Nat) :
    shiftedIntervalDot grad payload shift lo mid +
      shiftedIntervalDot grad payload shift (mid + 1) hi =
        shiftedIntervalDot grad payload shift lo hi := by
  unfold shiftedIntervalDot
  exact intervalSum_concat (shiftedProduct grad payload shift) lo mid hi

/-- Shifted contraction is the ordinary contraction of the pointwise shifted
payload. -/
theorem shiftedContraction_eq_contraction
    (grad base payload : Nat → Int) (shift : Int) (lo hi : Nat) :
    shiftedContraction grad base payload shift lo hi =
      contraction grad base (fun t => shiftedPayload payload shift t) lo hi := by
  unfold shiftedContraction shiftedIntervalDot shiftedProduct
  rw [contraction_eq_dot_sub]
  unfold intervalDot
  rfl

/-- Endpoint-level contraction expansion: `e(t)=t+s` reads payload at
`e(t)+1`, i.e. at `t+(s+1)`. -/
theorem endpointShiftContraction_eq_contraction
    (grad base payload : Nat → Int) (endpointShift : Int) (lo hi : Nat) :
    endpointShiftContraction grad base payload endpointShift lo hi =
      contraction grad base
        (fun t => shiftedPayload payload (endpointShift + 1) t) lo hi := by
  unfold endpointShiftContraction
  exact shiftedContraction_eq_contraction grad base payload (endpointShift + 1) lo hi

/-- The zero-shift case is an ordinary payload read. -/
theorem shiftedPayload_zero (payload : Nat → Int) (t : Nat) :
    shiftedPayload payload 0 t = payload t := by
  unfold shiftedPayload
  have h : 0 ≤ (t : Int) := Int.natCast_nonneg t
  simp [h]

/-- Zero-shift shifted contraction is ordinary contraction. -/
theorem shiftedContraction_zero
    (grad base payload : Nat → Int) (lo hi : Nat) :
    shiftedContraction grad base payload 0 lo hi =
      contraction grad base payload lo hi := by
  rw [shiftedContraction_eq_contraction]
  have hfun : (fun t => shiftedPayload payload 0 t) = payload := by
    funext t
    exact shiftedPayload_zero payload t
  rw [hfun]

/-! ## Winner intervals, accumulation, and exact telescoping -/

/-- A nonempty inclusive interval. -/
structure Interval where
  lo : Nat
  hi : Nat
  nonempty : lo ≤ hi
  deriving DecidableEq, Repr

/-- Adjacent intervals cover `[lo, hi]` exactly.  The empty tail is the
boundary condition `next = last + 1`. -/
inductive ChainFromTo : Nat → Nat → List Interval → Prop
  | nil {lo hi : Nat} (h : lo = hi + 1) : ChainFromTo lo hi []
  | cons {lo hi : Nat} (I : Interval) (rest : List Interval)
      (hstart : I.lo = lo)
      (hrest : ChainFromTo (I.hi + 1) hi rest) :
      ChainFromTo lo hi (I :: rest)

/-- Summing a pointwise sequence over adjacent winner intervals equals the
sum over the whole covered interval. -/
theorem chain_intervalSum (w : Nat → Int) {lo hi : Nat} {segments : List Interval}
    (h : ChainFromTo lo hi segments) :
    (segments.map (fun I => intervalSum w I.lo I.hi)).sum =
      intervalSum w lo hi := by
  induction segments generalizing lo hi with
  | nil =>
      cases h with
      | nil hnil =>
          rw [hnil]
          simp [intervalSum, prefixSum]
  | cons I rest ih =>
      cases h with
      | cons I' rest' hstart hrest =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih hrest]
          rw [← hstart]
          rw [← intervalSum_concat w I.lo I.hi hi]

/-- Winner-interval accumulation: the accumulated pointwise contribution over
an adjacent list of winning intervals equals the pointwise sum over the full
winner range. -/
theorem winnerIntervals_accum_eq_pointwise
    (w : Nat → Int) {lo hi : Nat} {segments : List Interval}
    (h : ChainFromTo lo hi segments) :
    (segments.map (fun I => intervalSum w I.lo I.hi)).sum =
      intervalSum w lo hi :=
  chain_intervalSum w h

/-- Accumulated interval payload dots over a winner chain equal the full
interval payload dot. -/
theorem chain_intervalDot
    (grad payload : Nat → Int) {lo hi : Nat} {segments : List Interval}
    (h : ChainFromTo lo hi segments) :
    (segments.map (fun I => intervalDot grad payload I.lo I.hi)).sum =
      intervalDot grad payload lo hi := by
  unfold intervalDot
  exact chain_intervalSum (fun t => grad t * payload t) h

/-- Accumulated contractions over a winner chain equal the full contraction. -/
theorem chain_contraction
    (grad base candidate : Nat → Int) {lo hi : Nat} {segments : List Interval}
    (h : ChainFromTo lo hi segments) :
    (segments.map (fun I => contraction grad base candidate I.lo I.hi)).sum =
      contraction grad base candidate lo hi := by
  unfold contraction
  exact chain_intervalSum (fun t => grad t * (candidate t - base t)) h

/-- Accumulated constant-endpoint contractions over a winner chain equal the
full constant-endpoint contraction. -/
theorem chain_constantEndpointContraction
    (grad base : Nat → Int) (c : Int)
    {lo hi : Nat} {segments : List Interval} (h : ChainFromTo lo hi segments) :
    (segments.map (fun I => constantEndpointContraction grad base c I.lo I.hi)).sum =
      constantEndpointContraction grad base c lo hi := by
  have hmap : (fun I : Interval => constantEndpointContraction grad base c I.lo I.hi) =
      (fun I : Interval => contraction grad base (fun _ => c) I.lo I.hi) := by
    funext I
    exact constantEndpointContraction_eq_contraction grad base c I.lo I.hi
  rw [hmap]
  rw [constantEndpointContraction_eq_contraction]
  exact chain_contraction grad base (fun _ => c) h

/-- A winner interval on which a discrete endpoint is constant. -/
def ConstantEndpointOn (endpoint : Nat → Int) (value : Int) (I : Interval) : Prop :=
  ∀ t, I.lo ≤ t → t ≤ I.hi → endpoint t = value

/-- A winner interval on which the endpoint is `t + shift`. -/
def ShiftedEndpointOn (endpoint : Nat → Int) (shift : Int) (I : Interval) : Prop :=
  ∀ t, I.lo ≤ t → t ≤ I.hi → endpoint t = (t : Int) + shift

/-- A validity predicate for the shifted read on a winner interval.  ROSA
reads `V[endpoint+1]`, so the guarded integer index is `endpoint+1`. -/
def ShiftedEndpointValid (endpoint : Nat → Int) (I : Interval) : Prop :=
  ∀ t, I.lo ≤ t → t ≤ I.hi → 0 ≤ endpoint t + 1

/-- If M3 marks an interval as a constant-endpoint winner, the factored
constant contraction is exactly the pointwise winner contraction on it. -/
theorem constantWinnerInterval_eq_pointwise
    (grad base payload : Nat → Int) (winnerEndpoint : Nat → Int) (value : Int)
    (I : Interval) (hconst : ConstantEndpointOn winnerEndpoint value I) :
    constantEndpointContraction grad base
        (payload (Int.toNat (value + 1))) I.lo I.hi =
      contraction grad base
        (fun t => payload (Int.toNat (winnerEndpoint t + 1))) I.lo I.hi := by
  rw [constantEndpointContraction_eq_contraction]
  rw [contraction_eq_dot_sub, contraction_eq_dot_sub]
  apply congrArg (fun z : Int => z - intervalDot grad base I.lo I.hi)
  apply intervalDot_congr_on grad (fun _ => payload (Int.toNat (value + 1)))
    (fun t => payload (Int.toNat (winnerEndpoint t + 1))) I.lo I.hi I.nonempty
  intro t h1 h2
  rw [hconst t h1 h2]

/-- If M3 marks an interval with `endpoint(t) = t + endpointShift`, the
endpoint-level contraction (runtime reads `V[endpoint+1]`) is exactly the
pointwise winner contraction on it, provided the shifted read index is in
range. -/
theorem endpointShiftWinnerInterval_eq_pointwise
    (grad base payload : Nat → Int) (winnerEndpoint : Nat → Int) (endpointShift : Int)
    (I : Interval) (hend : ShiftedEndpointOn winnerEndpoint endpointShift I)
    (hvalid : ShiftedEndpointValid winnerEndpoint I) :
    endpointShiftContraction grad base payload endpointShift I.lo I.hi =
      contraction grad base
        (fun t => payload (Int.toNat (winnerEndpoint t + 1))) I.lo I.hi := by
  unfold endpointShiftContraction
  rw [shiftedContraction_eq_contraction]
  rw [contraction_eq_dot_sub, contraction_eq_dot_sub]
  apply congrArg (fun z : Int => z - intervalDot grad base I.lo I.hi)
  apply intervalDot_congr_on grad (fun t => shiftedPayload payload (endpointShift + 1) t)
    (fun t => payload (Int.toNat (winnerEndpoint t + 1))) I.lo I.hi I.nonempty
  intro t h1 h2
  have hidx : (t : Int) + (endpointShift + 1) = winnerEndpoint t + 1 := by
    rw [hend t h1 h2]
    omega
  have hnonneg : 0 ≤ (t : Int) + (endpointShift + 1) := by
    rw [hidx]
    exact hvalid t h1 h2
  rw [shiftedPayload_eq_of_nonneg payload (endpointShift + 1) t hnonneg]
  rw [hidx]

/-- Accumulated shifted contractions over a winner chain equal the full
shifted contraction. -/
theorem chain_shiftedContraction
    (grad base payload : Nat → Int) (shift : Int)
    {lo hi : Nat} {segments : List Interval} (h : ChainFromTo lo hi segments) :
    (segments.map (fun I => shiftedContraction grad base payload shift I.lo I.hi)).sum =
      shiftedContraction grad base payload shift lo hi := by
  have hmap : (fun I : Interval => shiftedContraction grad base payload shift I.lo I.hi) =
      (fun I : Interval => contraction grad base
        (fun t => shiftedPayload payload shift t) I.lo I.hi) := by
    funext I
    exact shiftedContraction_eq_contraction grad base payload shift I.lo I.hi
  rw [hmap]
  rw [shiftedContraction_eq_contraction]
  exact chain_contraction grad base (fun t => shiftedPayload payload shift t) h

/-- Endpoint-level accumulation for `endpoint(t)=t+endpointShift` winner
intervals. -/
theorem chain_endpointShiftContraction
    (grad base payload : Nat → Int) (endpointShift : Int)
    {lo hi : Nat} {segments : List Interval} (h : ChainFromTo lo hi segments) :
    (segments.map (fun I =>
        endpointShiftContraction grad base payload endpointShift I.lo I.hi)).sum =
      endpointShiftContraction grad base payload endpointShift lo hi := by
  unfold endpointShiftContraction
  exact chain_shiftedContraction grad base payload (endpointShift + 1) h

end PayloadContraction

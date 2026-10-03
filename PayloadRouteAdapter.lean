import PayloadContraction
import Phase12b
import AffineLifetime
import BridgeEnvelope

/-!
## Adapter from affine winner intervals to M4 payload contraction

This file connects the event/interval layer used by M3 to the exact-integer
contraction algebra in `PayloadContraction`.  It does not make any claim about
`Float32` or `Float64` reduction order.
-/

namespace PayloadRouteAdapter

open Route RosBridge AffineLifetime
open PayloadContraction

/-- A `PayloadContraction.Interval` built from inclusive Nat bounds. -/
def intervalOfBounds (lo hi : Nat) (h : lo ≤ hi) : PayloadContraction.Interval :=
  ⟨lo, hi, h⟩

/-- The endpoint coordinate of a route-valued piece. -/
def routeEndpoint (F : Nat → Route) : Nat → Int :=
  fun t => (F t).endpoint

/-- Runtime-friendly affine endpoint `t ↦ slope * t + intercept`. -/
def affineEndpoint (slope intercept : Int) : Nat → Int :=
  fun t => slope * (t : Int) + intercept

/-- Endpoint function of a concrete repair bridge. -/
def bridgeEndpoint (b : Bridge) : Nat → Int :=
  routeEndpoint b.routeAt

/-- Interpret an abstract affine lifetime candidate as a route-valued function. -/
def candidateRoute (c : Candidate) : Nat → Route :=
  fun t => ⟨c.route.len (t : Int), c.route.ep (t : Int)⟩

/-- Endpoint function of an affine lifetime candidate on natural time indices. -/
def candidateEndpoint (c : Candidate) : Nat → Int :=
  routeEndpoint (candidateRoute c)

/-- Candidate endpoint coefficients are the runtime affine endpoint form. -/
theorem candidateEndpoint_eq_affineEndpoint (c : Candidate) :
    candidateEndpoint c = affineEndpoint c.route.aE c.route.bE := by
  rfl

/-- A constant endpoint has zero affine slope. -/
theorem affineEndpoint_constant (slope intercept : Int) (I : PayloadContraction.Interval)
    (hslope : slope = 0) :
    ConstantEndpointOn (affineEndpoint slope intercept) intercept I := by
  intro t _ _
  simp [affineEndpoint, hslope]

/-- A slope-one endpoint is a `t + intercept` shifted endpoint. -/
theorem affineEndpoint_shift (slope intercept : Int) (I : PayloadContraction.Interval)
    (hslope : slope = 1) :
    ShiftedEndpointOn (affineEndpoint slope intercept) intercept I := by
  intro t _ _
  simp [affineEndpoint, hslope]

/-- One affine route piece on an inclusive nonempty interval. -/
structure AffinePiece (F : Nat → Route) where
  kappa : Int × Int
  lo : Nat
  hi : Nat
  nonempty : lo ≤ hi
  affine : Phase12b.AffineOn F kappa lo hi

namespace AffinePiece

/-- Forget an `AffineOn` witness to the M4 interval/endpoint adapter piece. -/
def ofAffineOn {F : Nat → Route} {kappa : Int × Int} {lo hi : Nat}
    (hnonempty : lo ≤ hi) (haffine : Phase12b.AffineOn F kappa lo hi) :
    AffinePiece F where
  kappa := kappa
  lo := lo
  hi := hi
  nonempty := hnonempty
  affine := haffine

/-- The adapter interval for a route piece. -/
def interval {F : Nat → Route} (p : AffinePiece F) : PayloadContraction.Interval :=
  intervalOfBounds p.lo p.hi p.nonempty

/-- The endpoint function consumed by the M4 contraction layer. -/
def endpoint {F : Nat → Route} (_p : AffinePiece F) : Nat → Int :=
  routeEndpoint F

/-- An affine `routeOfKappa` piece has endpoint `t + (-kappa.2 - 1)`. -/
theorem shiftedEndpoint {F : Nat → Route} (p : AffinePiece F) :
    ShiftedEndpointOn p.endpoint (-p.kappa.2 - 1) p.interval := by
  intro t hlo hhi
  have hroute := p.affine t hlo hhi
  change (F t).endpoint = (t : Int) + (-p.kappa.2 - 1)
  rw [hroute]
  simp [Phase12b.routeOfKappa]
  omega

end AffinePiece

/-- A bridge's whole lifetime is one affine piece. -/
def bridgeAffinePiece (b : Bridge) : AffinePiece b.routeAt where
  kappa := b.kappa
  lo := b.p
  hi := b.p + b.R
  nonempty := by omega
  affine := Phase12b.bridge_affineOn b

/-- Endpoint-shift form of the bridge-to-M4 adapter. -/
theorem bridgeAffinePiece_shiftedEndpoint (b : Bridge) :
    ShiftedEndpointOn (bridgeEndpoint b) (-b.kappa.2 - 1)
      (bridgeAffinePiece b).interval := by
  exact (bridgeAffinePiece b).shiftedEndpoint

/-- The affine `kappa` shift and the runtime bridge endpoint shift coincide. -/
theorem bridge_kappa_endpointShift_eq_runtimeShift (b : Bridge) :
    -b.kappa.2 - 1 = (b.u : Int) - (b.p : Int) := by
  simp [RosBridge.Bridge.kappa]

/-- A constant endpoint on a piece is accepted directly by the M4 constant theorem. -/
theorem constantEndpointPiece_eq_pointwise
    (grad base payload : Nat → Int) {F : Nat → Route}
    (p : AffinePiece F) (value : Int)
    (hconst : ConstantEndpointOn p.endpoint value p.interval) :
    constantEndpointContraction grad base
        (payload (Int.toNat (value + 1))) p.interval.lo p.interval.hi =
      contraction grad base
        (fun t => payload (Int.toNat (p.endpoint t + 1)))
        p.interval.lo p.interval.hi := by
  exact constantWinnerInterval_eq_pointwise grad base payload p.endpoint value
    p.interval hconst

/-- A shifted endpoint on a piece is accepted directly by the M4 shifted theorem. -/
theorem endpointShiftPiece_eq_pointwise
    (grad base payload : Nat → Int) {F : Nat → Route}
    (p : AffinePiece F) (shift : Int)
    (hshift : ShiftedEndpointOn p.endpoint shift p.interval)
    (hvalid : ShiftedEndpointValid p.endpoint p.interval) :
    endpointShiftContraction grad base payload shift p.interval.lo p.interval.hi =
      contraction grad base
        (fun t => payload (Int.toNat (p.endpoint t + 1)))
        p.interval.lo p.interval.hi := by
  exact endpointShiftWinnerInterval_eq_pointwise grad base payload p.endpoint shift
    p.interval hshift hvalid

/-- A constant candidate endpoint (zero endpoint slope) on any M4 interval. -/
theorem candidateEndpoint_constant (c : Candidate) (I : PayloadContraction.Interval)
    (hslope : c.route.aE = 0) :
    ConstantEndpointOn (candidateEndpoint c) c.route.bE I := by
  intro t _ _
  change c.route.aE * (t : Int) + c.route.bE = c.route.bE
  rw [hslope]
  simp

/-- A slope-one candidate endpoint is exactly `t + c.route.bE`. -/
theorem candidateEndpoint_shift (c : Candidate) (I : PayloadContraction.Interval)
    (hslope : c.route.aE = 1) :
    ShiftedEndpointOn (candidateEndpoint c) c.route.bE I := by
  intro t _ _
  change c.route.aE * (t : Int) + c.route.bE = (t : Int) + c.route.bE
  rw [hslope]
  simp

/-- The candidate route induced by a bridge agrees with the concrete bridge route. -/
theorem ofBridge_candidateRoute_eq_routeAt (b : Bridge) (t : Nat) (h : b.Active t) :
    candidateRoute (AffineLifetime.ofBridge b) t = b.routeAt t := by
  apply Route.ext
  · exact AffineLifetime.ofBridge_routeAt_len b t h
  · exact AffineLifetime.ofBridge_routeAt_ep b t h

/-- Endpoint compatibility at every active natural time. -/
theorem ofBridge_candidateEndpoint_eq_bridgeEndpoint
    (b : Bridge) (t : Nat) (h : b.Active t) :
    candidateEndpoint (AffineLifetime.ofBridge b) t = bridgeEndpoint b t := by
  unfold candidateEndpoint bridgeEndpoint routeEndpoint
  rw [ofBridge_candidateRoute_eq_routeAt b t h]

/-- The bridge candidate has endpoint `t + (u - p)`. -/
theorem ofBridge_candidateEndpoint_shift (b : Bridge) :
    ShiftedEndpointOn (candidateEndpoint (AffineLifetime.ofBridge b))
      ((b.u : Int) - (b.p : Int)) (bridgeAffinePiece b).interval := by
  apply candidateEndpoint_shift
  rfl

/-- Coverage helper for a list of adjacent intervals. -/
theorem exists_interval_mem_of_chain
    {lo hi t : Nat} {segments : List PayloadContraction.Interval}
    (hchain : ChainFromTo lo hi segments) (htlo : lo ≤ t) (hthi : t ≤ hi) :
    ∃ I, I ∈ segments ∧ I.lo ≤ t ∧ t ≤ I.hi := by
  induction segments generalizing lo hi with
  | nil =>
      cases hchain with
      | nil hnil => omega
  | cons I rest ih =>
      cases hchain with
      | cons I' rest' hstart hrest =>
          by_cases hle : t ≤ I.hi
          · refine ⟨I, by simp, ?_, hle⟩
            rw [hstart]
            exact htlo
          · have hlt : I.hi < t := Nat.lt_of_not_ge hle
            have htlo' : I.hi + 1 ≤ t := Nat.succ_le_of_lt hlt
            rcases ih hrest htlo' hthi with ⟨J, hJ, hloJ, hhiJ⟩
            exact ⟨J, by simp [hJ], hloJ, hhiJ⟩

/-- A piecewise shifted endpoint is shifted on the covered whole interval. -/
theorem shiftedEndpointOn_of_chain
    {endpoint : Nat → Int} {shift : Int} {lo hi : Nat}
    {segments : List PayloadContraction.Interval}
    (hchain : ChainFromTo lo hi segments) (hfull : lo ≤ hi)
    (hpiece : ∀ I, I ∈ segments → ShiftedEndpointOn endpoint shift I) :
    ShiftedEndpointOn endpoint shift (intervalOfBounds lo hi hfull) := by
  intro t htlo hthi
  rcases exists_interval_mem_of_chain hchain htlo hthi with ⟨I, hI, hlo, hhi⟩
  exact hpiece I hI t hlo hhi

/-- A piecewise constant endpoint is constant on the covered whole interval. -/
theorem constantEndpointOn_of_chain
    {endpoint : Nat → Int} {value : Int} {lo hi : Nat}
    {segments : List PayloadContraction.Interval}
    (hchain : ChainFromTo lo hi segments) (hfull : lo ≤ hi)
    (hpiece : ∀ I, I ∈ segments → ConstantEndpointOn endpoint value I) :
    ConstantEndpointOn endpoint value (intervalOfBounds lo hi hfull) := by
  intro t htlo hthi
  rcases exists_interval_mem_of_chain hchain htlo hthi with ⟨I, hI, hlo, hhi⟩
  exact hpiece I hI t hlo hhi

/-- Piecewise shifted-read validity extends to the covered whole interval. -/
theorem shiftedEndpointValid_of_chain
    {endpoint : Nat → Int} {lo hi : Nat}
    {segments : List PayloadContraction.Interval}
    (hchain : ChainFromTo lo hi segments) (hfull : lo ≤ hi)
    (hpiece : ∀ I, I ∈ segments → ShiftedEndpointValid endpoint I) :
    ShiftedEndpointValid endpoint (intervalOfBounds lo hi hfull) := by
  intro t htlo hthi
  rcases exists_interval_mem_of_chain hchain htlo hthi with ⟨I, hI, hlo, hhi⟩
  exact hpiece I hI t hlo hhi

/-- The accumulated constant-endpoint contractions on a winner-interval chain
equal the exact pointwise contraction on the covered interval. -/
theorem constantEndpointWinnerChain_eq_pointwise
    (grad base payload : Nat → Int) (endpoint : Nat → Int) (value : Int)
    {lo hi : Nat} {segments : List PayloadContraction.Interval}
    (hchain : ChainFromTo lo hi segments) (hfull : lo ≤ hi)
    (hpiece : ∀ I, I ∈ segments → ConstantEndpointOn endpoint value I) :
    (segments.map (fun I =>
        constantEndpointContraction grad base
          (payload (Int.toNat (value + 1))) I.lo I.hi)).sum =
      contraction grad base
        (fun t => payload (Int.toNat (endpoint t + 1))) lo hi := by
  let full : PayloadContraction.Interval := intervalOfBounds lo hi hfull
  have hpieceFull : ConstantEndpointOn endpoint value full :=
    constantEndpointOn_of_chain hchain hfull hpiece
  rw [chain_constantEndpointContraction grad base (payload (Int.toNat (value + 1))) hchain]
  exact constantWinnerInterval_eq_pointwise grad base payload endpoint value
    full hpieceFull

/-- The accumulated shifted contractions on a winner-interval chain equal the
exact pointwise contraction on the covered interval, provided every piece has
the same endpoint shift and an in-range payload read. -/
theorem endpointShiftWinnerChain_eq_pointwise
    (grad base payload : Nat → Int) (endpoint : Nat → Int) (shift : Int)
    {lo hi : Nat} {segments : List PayloadContraction.Interval}
    (hchain : ChainFromTo lo hi segments) (hfull : lo ≤ hi)
    (hpiece : ∀ I, I ∈ segments → ShiftedEndpointOn endpoint shift I)
    (hvalid : ∀ I, I ∈ segments → ShiftedEndpointValid endpoint I) :
    (segments.map (fun I =>
        endpointShiftContraction grad base payload shift I.lo I.hi)).sum =
      contraction grad base
        (fun t => payload (Int.toNat (endpoint t + 1))) lo hi := by
  let full : PayloadContraction.Interval := intervalOfBounds lo hi hfull
  have hpieceFull : ShiftedEndpointOn endpoint shift full :=
    shiftedEndpointOn_of_chain hchain hfull hpiece
  have hvalidFull : ShiftedEndpointValid endpoint full :=
    shiftedEndpointValid_of_chain hchain hfull hvalid
  rw [chain_endpointShiftContraction grad base payload shift hchain]
  exact endpointShiftWinnerInterval_eq_pointwise grad base payload endpoint shift
    full hpieceFull hvalidFull

/-- Piecewise form of the same result: each shifted winner piece is replaced by
its exact pointwise contraction before the chain is summed. -/
theorem endpointShiftWinnerChain_eq_pointwiseSum
    (grad base payload : Nat → Int) (endpoint : Nat → Int) (shift : Int)
    {segments : List PayloadContraction.Interval}
    (hpiece : ∀ I, I ∈ segments → ShiftedEndpointOn endpoint shift I)
    (hvalid : ∀ I, I ∈ segments → ShiftedEndpointValid endpoint I) :
    (segments.map (fun I =>
        endpointShiftContraction grad base payload shift I.lo I.hi)).sum =
      (segments.map (fun I =>
        contraction grad base
          (fun t => payload (Int.toNat (endpoint t + 1))) I.lo I.hi)).sum := by
  congr 1
  apply List.map_congr_left
  intro I hI
  exact endpointShiftWinnerInterval_eq_pointwise grad base payload endpoint shift I
    (hpiece I hI) (hvalid I hI)

end PayloadRouteAdapter

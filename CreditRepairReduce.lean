import Std
import RosBridge
import Repair
import RunRectangleLcp

/-!
## Exact ROSA credit — §1 of `ROSA_Credit_New_Results`

*"严格内部 Q-owner：三个候选进一步降为两个"* — a Q-owner `p` that is **strictly
interior** to its Q-run has, for every one-bit `Q`-repair pair, only the K right
end `d` able to carry a positive right context.  Hence among the three
representative repair bridges (`K` left end `c`, `K` right end `d`, interior
maximal causal end `min (d-1) (p-1)`) at most one survives past the birth instant
`p`, and keeping

* the bridge that is optimal at the common birth instant `p`, and
* the unique bridge that outlives `p`

reproduces the entire repair envelope.

This file is deliberately written on top of the *existing* Phase-F/G results:

* `Repair.repair_right_boundary_support` (the R-side Boundary-Support theorem)
  already states that a positive right context forces `p = b ∨ u = d`; the new
  content here is the contrapositive reading used by the credit algorithm
  (`R > 0 ⇒ u = d`), plus the candidate-list compression.
* `RosBridge.Bridge` supplies the bridge semantics, the birth/death lifetime and
  the time-independent priority `κ` used by `RosBridge.Bridge.bridge_kappa_const`.

Nothing here is ROSA-specific beyond `RunRect.ConstRun`: the statements are about
a Q-run `[a,b]` with symbol `αs` and a K-run `[c,d]` with symbol `βs ≠ αs`.
-/

namespace CreditRepair

open Lcs RunRect Repair RosBridge

variable {α : Type} [DecidableEq α]

/-! ### The repair bridge of a causal centre -/

/-- The repair bridge `(p,u,L,R)` of the causal centre `(p,u)` with `L = leftCtx`
and `R = rightCtx`.  This is exactly `RunContexts.bridge` of
`rosa_repair_core.py` (`return (p, p + right, 1, left + 1 - p, 1, u - p)`). -/
def ctxBridge (q k : Nat → α) (Tq Tk p u : Nat) : Bridge :=
  ⟨p, u, leftCtx q k p u, rightCtx q k Tq Tk p u⟩

@[simp] theorem ctxBridge_p (q k : Nat → α) (Tq Tk p u : Nat) :
    (ctxBridge q k Tq Tk p u).p = p := rfl

@[simp] theorem ctxBridge_u (q k : Nat → α) (Tq Tk p u : Nat) :
    (ctxBridge q k Tq Tk p u).u = u := rfl

@[simp] theorem ctxBridge_L (q k : Nat → α) (Tq Tk p u : Nat) :
    (ctxBridge q k Tq Tk p u).L = leftCtx q k p u := rfl

@[simp] theorem ctxBridge_R (q k : Nat → α) (Tq Tk p u : Nat) :
    (ctxBridge q k Tq Tk p u).R = rightCtx q k Tq Tk p u := rfl

@[simp] theorem ctxBridge_death (q k : Nat → α) (Tq Tk p u : Nat) :
    (ctxBridge q k Tq Tk p u).death = p + rightCtx q k Tq Tk p u := rfl

@[simp] theorem ctxBridge_birth (q k : Nat → α) (Tq Tk p u : Nat) :
    (ctxBridge q k Tq Tk p u).birth = p := rfl

/-! ### §1, core geometry: `R > 0 ⇒ u = d` -/

/-- **Strictly interior Q-centre, non-right-end K-centre ⇒ zero right context.**
Contrapositive of the existing R-side Boundary-Support theorem:
`0 < lcpLen → p = b ∨ u = d`. -/
theorem right_ctx_zero_of_not_right_end {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p u : Nat} (hpa : a ≤ p) (hpb : p ≤ b) (huc : c ≤ u) (hud : u ≤ d)
    (hpb' : p < b) (hud' : u < d) :
    lcpLen q k Tq Tk p u = 0 := by
  by_cases h : lcpLen q k Tq Tk p u = 0
  · exact h
  · exfalso
    have hpos : 0 < lcpLen q k Tq Tk p u := by omega
    rcases repair_right_boundary_support hQ hK hne hpa hpb huc hud hpos with h' | h' <;> omega

/-- **§1: `R > 0 ⟹ u = d`.**  A bridge born at a Q-centre strictly inside its run
cannot carry a right context unless it uses the K-run's right end. -/
theorem carry_forces_k_right_end {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p u : Nat} (hpa : a ≤ p) (hpb : p ≤ b) (huc : c ≤ u) (hud : u ≤ d)
    (hpb' : p < b) (hR : 0 < (ctxBridge q k Tq Tk p u).R) :
    u = d := by
  have hpos : 0 < lcpLen q k Tq Tk p u := hR
  rcases repair_right_boundary_support hQ hK hne hpa hpb huc hud hpos with h' | h' <;> omega

/-! ### §1, candidate compression: the three representative centres -/

/-- The three representative K-centres of a strict-interior Q-owner (§1): the
K-run's left end `c`, its right end `d`, and the interior maximal causal end
`min (d-1) (p-1)`. -/
def qOwnerCenters (p c d : Nat) : List Nat := [c, d, min (d - 1) (p - 1)]

/-- The repair bridges of the representative centres that actually exist
(`c ≤ u ≤ d` and causal `u < p`).  This is `initial` in
`rosa_repair_core.py:repair_core`. -/
def qOwnerBridges (q k : Nat → α) (Tq Tk p c d : Nat) : List Bridge :=
  ((qOwnerCenters p c d).filter (fun u => decide (c ≤ u ∧ u ≤ d ∧ u < p))).map
    (fun u => ctxBridge q k Tq Tk p u)

/-- **Only the K-right-end representative can outlive the birth instant.** -/
theorem qOwnerBridges_carry_unique {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p : Nat} (hpa : a ≤ p) (hpb : p ≤ b) (hpb' : p < b)
    {β : Bridge} (hβ : β ∈ qOwnerBridges q k Tq Tk p c d) (hcarry : p < β.death) :
    β.u = d := by
  rw [qOwnerBridges, List.mem_map] at hβ
  obtain ⟨u, hu, hbu⟩ := hβ
  rw [List.mem_filter] at hu
  obtain ⟨_, huP⟩ := hu
  simp only [decide_eq_true_eq] at huP
  obtain ⟨hcu, hud, _⟩ := huP
  by_cases hud' : u < d
  · have hd : p < (ctxBridge q k Tq Tk p u).death := by
      rw [hbu]; exact hcarry
    have hR : 0 < (ctxBridge q k Tq Tk p u).R := by
      have hd' := hd
      simp only [ctxBridge_death] at hd'
      have hne0 : rightCtx q k Tq Tk p u ≠ 0 := by
        intro h0
        rw [h0, Nat.add_zero] at hd'
        omega
      simpa [ctxBridge_R] using Nat.pos_of_ne_zero hne0
    have hfin := carry_forces_k_right_end hQ hK hne hpa hpb hcu hud hpb' hR
    rw [← hbu]
    simpa using hfin
  · have : u = d := by omega
    rw [← hbu]
    simpa using this

/-! ### §1, conclusion: two candidates reproduce the whole envelope -/

/-- The live routes of a bridge list at time `t`. -/
def activeRoutes (cs : List Bridge) (t : Nat) : List Route :=
  (cs.filter (fun b => decide (b.Active t))).map (fun b => b.routeAt t)

/-- Two lists of valid routes dominate each other elementwise iff their ROSA
maxima agree. -/
theorem rmaxList_eq_of_le {l₁ l₂ : List Route}
    (hv₁ : ∀ r ∈ l₁, Route.Valid r) (hv₂ : ∀ r ∈ l₂, Route.Valid r)
    (hl₁ : ∀ r ∈ l₁, Route.rle r (Route.rmaxList l₂))
    (hl₂ : ∀ r ∈ l₂, Route.rle r (Route.rmaxList l₁)) :
    Route.rmaxList l₁ = Route.rmaxList l₂ :=
  Route.rle_antisymm _ _
    (Route.rmaxList_lub l₁ (Route.rmaxList l₂) (Route.valid_rmaxList l₂ hv₂) hl₁)
    (Route.rmaxList_lub l₂ (Route.rmaxList l₁) (Route.valid_rmaxList l₁ hv₁) hl₂)

/-- **§1, final form.**  Let `cs` be the candidate bridges of a Q-owner that all
share the birth instant `p`, with `k₁` optimal at `p` and `k₂` the unique bridge
that outlives `p` (`p < b.death → b = k₂`).  Then the two retained candidates
`[k₁, k₂]` reproduce the ROSA winner at every `t ≥ p`. -/
theorem two_candidates_reproduce_envelope (cs : List Bridge) (p : Nat) (k₁ k₂ : Bridge)
    (hbirth : ∀ b ∈ cs, b.p = p)
    (hk₁ : k₁ ∈ cs) (hk₂ : k₂ ∈ cs)
    (hk₁max : ∀ b ∈ cs, Route.rle (b.routeAt p) (k₁.routeAt p))
    (hsurv : ∀ b ∈ cs, p < b.death → b = k₂) :
    ∀ t, p ≤ t →
      Route.rmaxList (activeRoutes cs t) = Route.rmaxList (activeRoutes [k₁, k₂] t) := by
  intro t ht
  have memA : ∀ {r : Route}, r ∈ activeRoutes cs t →
      ∃ b, b ∈ cs ∧ b.p ≤ t ∧ t ≤ b.p + b.R ∧ r = b.routeAt t := by
    intro r hr
    rw [activeRoutes, List.mem_map] at hr
    obtain ⟨b, hb, hbr⟩ := hr
    rw [List.mem_filter] at hb
    obtain ⟨hbcs, hbact⟩ := hb
    simp only [Bridge.Active] at hbact
    obtain ⟨hb1, hb2⟩ := of_decide_eq_true hbact
    exact ⟨b, hbcs, hb1, hb2, hbr.symm⟩
  have memB : ∀ {r : Route}, r ∈ activeRoutes [k₁, k₂] t →
      ∃ b, (b = k₁ ∨ b = k₂) ∧ b.p ≤ t ∧ t ≤ b.p + b.R ∧ r = b.routeAt t := by
    intro r hr
    rw [activeRoutes, List.mem_map] at hr
    obtain ⟨b, hb, hbr⟩ := hr
    rw [List.mem_filter] at hb
    obtain ⟨hb12, hbact⟩ := hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb12
    simp only [Bridge.Active] at hbact
    obtain ⟨hb1, hb2⟩ := of_decide_eq_true hbact
    exact ⟨b, hb12, hb1, hb2, hbr.symm⟩
  have activeAtP : ∀ b ∈ cs, b.p ≤ p ∧ p ≤ p + b.R := by
    intro b hb
    have hp : b.p = p := hbirth b hb
    rw [hp]
    exact ⟨Nat.le_refl p, Nat.le_add_right p b.R⟩
  have memB_k₁ : k₁.routeAt p ∈ activeRoutes [k₁, k₂] p := by
    rw [activeRoutes, List.mem_map]
    refine ⟨k₁, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨by simp, by simp [Bridge.Active, hbirth k₁ hk₁, activeAtP k₁ hk₁]⟩
  have memA_k₁ : k₁.routeAt p ∈ activeRoutes cs p := by
    rw [activeRoutes, List.mem_map]
    refine ⟨k₁, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨hk₁, by simp [Bridge.Active, hbirth k₁ hk₁, activeAtP k₁ hk₁]⟩
  apply rmaxList_eq_of_le
  · intro r hr
    obtain ⟨b, _, hb1, hb2, rfl⟩ := memA hr
    exact Bridge.valid_routeAt b t ⟨hb1, hb2⟩
  · intro r hr
    obtain ⟨b, _, hb1, hb2, rfl⟩ := memB hr
    exact Bridge.valid_routeAt b t ⟨hb1, hb2⟩
  · intro r hr
    obtain ⟨b, hbcs, hb1, hb2, rfl⟩ := memA hr
    by_cases hpt : t = p
    · subst hpt
      exact Route.rle_trans _ _ _ (hk₁max b hbcs) (Route.rle_rmaxList _ _ memB_k₁)
    · have hpt' : p < t := by omega
      have hbd : p < b.death := by
        have hp : b.p = p := hbirth b hbcs
        show p < b.p + b.R
        omega
      have hbeq : b = k₂ := hsurv b hbcs hbd
      subst b
      refine Route.rle_rmaxList _ _ ?_
      rw [activeRoutes, List.mem_map]
      refine ⟨k₂, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨by simp, decide_eq_true (show k₂.Active t from ⟨hb1, hb2⟩)⟩
  · intro r hr
    obtain ⟨b, hb12, hb1, hb2, rfl⟩ := memB hr
    rcases hb12 with hb1' | hb2'
    · cases hb1'
      by_cases hpt : t = p
      · subst hpt
        exact Route.rle_rmaxList _ _ memA_k₁
      · have hbd : p < k₁.death := by
          have hp : k₁.p = p := hbirth k₁ hk₁
          show p < k₁.p + k₁.R
          omega
        have hbeq : k₁ = k₂ := hsurv k₁ hk₁ hbd
        subst k₁
        refine Route.rle_rmaxList _ _ ?_
        rw [activeRoutes, List.mem_map]
        refine ⟨k₂, ?_, rfl⟩
        rw [List.mem_filter]
        exact ⟨hk₂, decide_eq_true (show k₂.Active t from ⟨hb1, hb2⟩)⟩
    · cases hb2'
      refine Route.rle_rmaxList _ _ ?_
      rw [activeRoutes, List.mem_map]
      refine ⟨k₂, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨hk₂, decide_eq_true (show k₂.Active t from ⟨hb1, hb2⟩)⟩

end CreditRepair

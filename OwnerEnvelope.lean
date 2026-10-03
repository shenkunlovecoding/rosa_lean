import Std
import AffineEnvelope
import Repair

/-!
## Phase H — finite-template owner envelope + gluing

Builds on `AffineEnvelope` (ROSA-independent affine route envelopes).

* **Step 2 (finite templates ⇒ `O(1)` owner envelope).**  For a finite candidate
  list, the winner set of any candidate is an interval, so the envelope has at
  most one piece per candidate.
* **Step 3 (global multi-run gluing).**  Concatenating candidate lists (the
  `A`/`P`/`U` directions: left-to-right carry / threshold records / union)
  preserves the interval winner set — the global envelope is again an interval.
-/

namespace OwnerEnv

open AffEnv
open Lcs RunRect Repair
open AffEnv.AffRoute

/-! ### Step 2 — finite templates ⇒ `O(1)` owner envelope -/

/-- `f` is the (lex) argmax over the candidate list `cs` at `t`. -/
def envWins (f : AffRoute) (cs : List AffRoute) (t : Int) : Prop := ∀ g ∈ cs, f.wins g t

/-- **Owner envelope is an interval.**  With a finite template list `cs`, the set
where `f` is the winner is an intersection of intervals, hence an interval: the
envelope has at most one piece per template. -/
theorem envWins_interval (f : AffRoute) (cs : List AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      envWins f cs t1 → envWins f cs t3 → envWins f cs t2 := by
  intro t1 t2 t3 _ h12 h23 _ h1 h3
  exact wins_list_convex f cs t1 t2 t3 h12 h23 h1 h3

/-- One-switch corollary: over two affine routes, `g` beats `f` on a single
interval (this is the "winner 只切一次或至多两次" phenomenon). -/
theorem two_winner_interval (f g : AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      g.wins f t1 → g.wins f t3 → g.wins f t2 := by
  intro t1 t2 t3 _ h12 h23 _ h1 h3
  exact wins_convex g f t1 t2 t3 h12 h23 h1 h3

/-! ### One-bit run-pair template library (§9)

All shapes that occur inside one one-bit run rectangle are affine routes:
`constant` / `slope +1` / `slope -1` / `RSP` pieces / `single spike` /
`bounded affine segment`. -/

/-- Bridge route (§9.1): flip the centre `(p,u)` and the bridge is active on
`t ∈ [p, p+R]` with `ℓ(t) = L+1+(t-p)`, `r(t) = u+(t-p)` — affine, slope `(1,1)`. -/
def bridgeRoute (L u p : Int) : AffRoute := ⟨1, L + 1 - p, 1, u - p⟩

/-- A single spike / interior bulk value: constant route. -/
def spikeRoute (v w : Int) : AffRoute := ⟨0, v, 0, w⟩

/-- A ramp piece: `ℓ` slope `+1`, `r` constant. -/
def rampRoute (bL w : Int) : AffRoute := ⟨1, bL, 0, w⟩

/-- A plateau piece: `ℓ` constant, `r` slope `+1`. -/
def plateauRoute (v bE : Int) : AffRoute := ⟨0, v, 1, bE⟩

/-- The `RSP` edge context of §9.5: ramp + single spike + plateau. -/
def rspTemplates (bL w bE : Int) : List AffRoute :=
  [rampRoute bL w, spikeRoute w bE, plateauRoute w bE]

/-! ### Step 3 — global multi-run gluing -/

/-- **Gluing.**  Concatenating the candidate lists of two runs preserves the
winner predicate: the global winner set is the intersection of the two. -/
theorem envWins_append (f : AffRoute) (l1 l2 : List AffRoute) (t : Int) :
    envWins f (l1 ++ l2) t ↔ envWins f l1 t ∧ envWins f l2 t := by
  unfold envWins
  constructor
  · intro h
    exact ⟨fun g hg => h g (by rw [List.mem_append]; exact Or.inl hg),
           fun g hg => h g (by rw [List.mem_append]; exact Or.inr hg)⟩
  · rintro ⟨h1, h2⟩ g hg
    rw [List.mem_append] at hg
    exact hg.elim (h1 g) (h2 g)

/-- **`A` — left-to-right carry.**  Prefix gluing is list concatenation. -/
theorem glue_A_leftToRight (f : AffRoute) (l1 l2 : List AffRoute) (t : Int) :
    envWins f (l1 ++ l2) t ↔ envWins f l1 t ∧ envWins f l2 t :=
  envWins_append f l1 l2 t

/-- **`P` — threshold records suffix-max.**  A threshold selects a sublist, and
selection commutes with concatenation, so gluing is again concatenation. -/
theorem glue_P_threshold (f : AffRoute) (thr : AffRoute → Int) (s : Int)
    (l1 l2 : List AffRoute) (t : Int) :
    envWins f ((l1 ++ l2).filter (fun c => decide (s < thr c))) t ↔
      envWins f (l1.filter (fun c => decide (s < thr c))) t ∧
        envWins f (l2.filter (fun c => decide (s < thr c))) t := by
  rw [List.filter_append, envWins_append]

/-- **`U` — plateau-interval union + prefix-max.**  Same for any sublist
selection (the plateau `δ`-intervals are unioned before the prefix max). -/
theorem glue_U_union (f : AffRoute) (sel : AffRoute → Bool)
    (l1 l2 : List AffRoute) (t : Int) :
    envWins f ((l1 ++ l2).filter sel) t ↔
      envWins f (l1.filter sel) t ∧ envWins f (l2.filter sel) t := by
  rw [List.filter_append, envWins_append]

/-- **Global gluing corollary.**  The owner envelope over any concatenation of
runs is still an interval (so the whole-row envelope is `O(#templates)` pieces). -/
theorem glue_interval (f : AffRoute) (l1 l2 : List AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      envWins f (l1 ++ l2) t1 → envWins f (l1 ++ l2) t3 →
        envWins f (l1 ++ l2) t2 :=
  envWins_interval f (l1 ++ l2) lo hi


/-! ### ROSA side of step 2: run-pair bridges reduce to templates

The §9.4 interior bulk descriptor: a strict-interior centre has `L = R = 0`, so
its bridge is a single-point constant template `(1,u)` — neither the interior
`Θ(mn)` centres nor the string semantics are needed downstream. -/

theorem interior_bridge_value {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    [DecidableEq α]
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p u : Nat} (hap : a < p) (hpb : p < b) (huc : c < u) (hud : u < d) :
    (bridgeRoute (lcsLen q k (p - 1) (u - 1) : Int) (u : Int) (p : Int)).len (p : Int) = 1 ∧
    (bridgeRoute (lcsLen q k (p - 1) (u - 1) : Int) (u : Int) (p : Int)).ep (p : Int) = (u : Int) := by
  obtain ⟨hL, _⟩ := repair_strict_interior_trivial hQ hK hne hap hpb huc hud
  have hL0 : (lcsLen q k (p - 1) (u - 1) : Int) = 0 := by rw [hL]; rfl
  constructor
  · simp only [bridgeRoute, len]; rw [hL0]; omega
  · simp only [bridgeRoute, ep]; omega

/-! ### §9.5 edge/corner enumeration + counts (step 1, closed) -/

/-- Causal one-bit centres `(p,u)` of a run pair: `p∈[a,b]`, `u∈[c,d]`, `u < p`. -/
def centers (a b c d : Nat) : List (Nat × Nat) :=
  ((List.range (b - a + 1)).map (fun i => a + i)).flatMap (fun p =>
    (((List.range (d - c + 1)).map (fun j => c + j)).filter (fun u => decide (u < p))).map
      (fun u => (p, u)))

/-- Bridge-route candidates of a run pair (§9.1), one `AffRoute` per causal centre. -/
def runPairCands (q k : Nat → α) [DecidableEq α] (a b c d : Nat) : List AffRoute :=
  (centers a b c d).map (fun pu =>
    bridgeRoute (leftCtx q k pu.1 pu.2 : Int) (pu.2 : Int) (pu.1 : Int))

/-- The owner envelope over a run pair's bridges is an interval. -/
theorem runPairCands_interval (q k : Nat → α) [DecidableEq α] (a b c d : Nat) (f : AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      envWins f (runPairCands q k a b c d) t1 → envWins f (runPairCands q k a b c d) t3 →
        envWins f (runPairCands q k a b c d) t2 :=
  envWins_interval f _ lo hi

/-- **Historical nine-slot skeleton.**  The corrected semantic version is
`OwnerTemplateEquivalence.runPairOwnerTemplates`; its equality with the actual
bridge field is proved by `runPairTemplates_corrected_max_eq_actual`.  This old
definition is retained only for the original size-count theorem. -/
def runPairTemplates (interior : AffRoute) (e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄ : AffRoute) : List AffRoute :=
  [interior, e₁, e₂, e₃, e₄, k₁, k₂, k₃, k₄]

/-- `O(1)` templates per run pair. -/
theorem runPairTemplates_length (interior e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄ : AffRoute) :
    (runPairTemplates interior e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄).length ≤ 9 := by
  simp [runPairTemplates]

/-- Owner envelope over the collapsed run-pair templates is an interval
(`O(1)` pieces per run pair). -/
theorem runPairTemplates_interval (interior e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄ : AffRoute)
    (f : AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      envWins f (runPairTemplates interior e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄) t1 →
      envWins f (runPairTemplates interior e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄) t3 →
        envWins f (runPairTemplates interior e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄) t2 :=
  envWins_interval f _ lo hi

/-- §9.4 interior collapse: any two strict-interior centres give the same birth
value `(1,u)`, so the `Θ(mn)` interior bulk is one template. -/
theorem interior_same_birth {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    [DecidableEq α]
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (hne : αs ≠ βs)
    {p p' u : Nat} (hap : a < p) (hpb : p < b) (hap' : a < p') (hpb' : p' < b)
    (huc : c < u) (hud : u < d) :
    (bridgeRoute (lcsLen q k (p - 1) (u - 1) : Int) (u : Int) (p : Int)).len (p : Int) =
      (bridgeRoute (lcsLen q k (p' - 1) (u - 1) : Int) (u : Int) (p' : Int)).len (p' : Int) ∧
    (bridgeRoute (lcsLen q k (p - 1) (u - 1) : Int) (u : Int) (p : Int)).ep (p : Int) =
      (bridgeRoute (lcsLen q k (p' - 1) (u - 1) : Int) (u : Int) (p' : Int)).ep (p' : Int) := by
  obtain ⟨h1, h2⟩ := interior_bridge_value hQ hK hne hap hpb huc hud
  obtain ⟨h3, h4⟩ := interior_bridge_value hQ hK hne hap' hpb' huc hud
  exact ⟨by rw [h1, h3], by rw [h2, h4]⟩

/-- **`O(R_K)` over the whole row.**  Each of the `R_K` run pairs contributes a
bounded template list; gluing preserves the interval winner set (`glue_interval`),
so the row owner envelope has at most `9 · R_K` pieces. -/
theorem row_interval (runs : List (List AffRoute)) (f : AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      envWins f runs.flatten t1 → envWins f runs.flatten t3 → envWins f runs.flatten t2 :=
  envWins_interval f runs.flatten lo hi

/-! ### Owner-restricted candidates

A real ROSA backward fixes an **owner** and a **bit**, then compares only that
perturbation's repair bridges; bridges of different owners do not compete.
`qOwnerCands` (fixed Q-owner `p`) and `kOwnerCands` (fixed K-owner `u`) split the
run-pair candidate list accordingly. -/

/-- Repair bridges with a fixed Q-owner `p` (K-side endpoints `u < p` vary). -/
def qOwnerCands (q k : Nat → α) [DecidableEq α] (p : Nat) (c d : Nat) : List AffRoute :=
  (((List.range (d - c + 1)).map (fun j => c + j)).filter (fun u => decide (u < p))).map
    (fun u => bridgeRoute (leftCtx q k p u : Int) (u : Int) (p : Int))

/-- Repair bridges with a fixed K-owner `u` (Q-side centres `p > u` vary). -/
def kOwnerCands (q k : Nat → α) [DecidableEq α] (u : Nat) (a b : Nat) : List AffRoute :=
  (((List.range (b - a + 1)).map (fun i => a + i)).filter (fun p => decide (u < p))).map
    (fun p => bridgeRoute (leftCtx q k p u : Int) (u : Int) (p : Int))

theorem qOwnerCands_interval (q k : Nat → α) [DecidableEq α] (p c d : Nat)
    (f : AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      envWins f (qOwnerCands q k p c d) t1 → envWins f (qOwnerCands q k p c d) t3 →
        envWins f (qOwnerCands q k p c d) t2 :=
  envWins_interval f _ lo hi

theorem kOwnerCands_interval (q k : Nat → α) [DecidableEq α] (u a b : Nat)
    (f : AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      envWins f (kOwnerCands q k u a b) t1 → envWins f (kOwnerCands q k u a b) t3 →
        envWins f (kOwnerCands q k u a b) t2 :=
  envWins_interval f _ lo hi

/-! ### Limitation: candidates have lifetimes

`envWins` models candidates active on the **whole** domain.  A real bridge lives
on `[p, p+R]`, and with differing lifetimes the winner set need not be an
interval — so `envWins_interval`/`row_interval` are a *common-domain* model, and
the real ROSA owner envelope needs a skyline/lifetime ordering on top. -/

/-- A candidate together with its active interval. -/
structure ActiveCand where
  r : AffRoute
  lo : Int
  hi : Int

/-- `f` wins over every candidate active at `t`. -/
def envWinsActive (f : AffRoute) (cs : List ActiveCand) (t : Int) : Prop :=
  ∀ c ∈ cs, c.lo ≤ t → t ≤ c.hi → f.wins c.r t

/-- **The interval property genuinely fails without lifetime assumptions.**  A
constant route `f` (always active) loses to a stronger `g` that is active only on
`[4,6]`; so `f` wins at `0` and `10` but not at `5`. -/
theorem active_not_interval :
    envWinsActive ⟨0, 5, 0, 0⟩ [⟨⟨0, 5, 0, 0⟩, -100, 100⟩, ⟨⟨0, 9, 0, 0⟩, 4, 6⟩] 0
      ∧ envWinsActive ⟨0, 5, 0, 0⟩ [⟨⟨0, 5, 0, 0⟩, -100, 100⟩, ⟨⟨0, 9, 0, 0⟩, 4, 6⟩] 10
      ∧ ¬ envWinsActive ⟨0, 5, 0, 0⟩ [⟨⟨0, 5, 0, 0⟩, -100, 100⟩, ⟨⟨0, 9, 0, 0⟩, 4, 6⟩] 5 := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc hl hh
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr ⟨rfl, by simp [AffRoute.ep]⟩
    · exact absurd hl (by decide)
  · intro c hc hl hh
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr ⟨rfl, by simp [AffRoute.ep]⟩
    · exact absurd hh (by decide)
  · intro h
    have hg := h ⟨⟨0, 9, 0, 0⟩, 4, 6⟩ (by simp) (by decide) (by decide)
    simp [AffRoute.wins, AffRoute.len] at hg

end OwnerEnv

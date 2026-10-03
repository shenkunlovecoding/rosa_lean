import Std

/-!
## Phase H — affine Route envelopes (ROSA-independent core)

A minimal abstract class: an *affine route* on an integer interval,

  `len(t) = aL*t + bL`,  `endpoint(t) = aE*t + bE`,   (`t : Int`)

compared by ROSA's lexicographic priority `(len, endpoint)`.

The core, completely string-free lemma: for two affine routes the RO SA
winner set is an **interval** — the length difference `Δ_L` is a 1-D affine
function (sign changes at most once), and only where `Δ_L = 0` does the affine
endpoint difference `Δ_E` enter the tie-break.  Hence `max(f,g)` has at most a
constant number of breakpoints.
-/

namespace AffEnv

/-! ### Pure affine arithmetic -/

theorem aff_sub (a b t1 t2 : Int) : (a * t2 + b) - (a * t1 + b) = a * (t2 - t1) := by
  rw [Int.mul_sub]; omega

theorem aff_mono (a b : Int) (ha : 0 ≤ a) {t1 t2 : Int} (ht : t1 ≤ t2) :
    a * t1 + b ≤ a * t2 + b := by
  have h := Int.mul_le_mul_of_nonneg_left (a := t1) (b := t2) (c := a) ht ha
  omega

theorem aff_anti (a b : Int) (ha : a ≤ 0) {t1 t2 : Int} (ht : t1 ≤ t2) :
    a * t2 + b ≤ a * t1 + b := by
  have h := Int.mul_le_mul_of_nonpos_left (a := a) (b := t2) (c := t1) ha ht
  omega

theorem aff_le_max (a b t1 t2 t3 : Int) (h12 : t1 ≤ t2) (h23 : t2 ≤ t3) :
    a * t2 + b ≤ max (a * t1 + b) (a * t3 + b) := by
  by_cases ha : 0 ≤ a
  · have := aff_mono a b ha h23; omega
  · have ha' : a ≤ 0 := by omega
    have := aff_anti a b ha' h12; omega

theorem aff_min_le (a b t1 t2 t3 : Int) (h12 : t1 ≤ t2) (h23 : t2 ≤ t3) :
    min (a * t1 + b) (a * t3 + b) ≤ a * t2 + b := by
  by_cases ha : 0 ≤ a
  · have := aff_mono a b ha h12; omega
  · have ha' : a ≤ 0 := by omega
    have := aff_anti a b ha' h23; omega

theorem aff_mul_eq_zero {a t1 t2 : Int} (h : a * (t2 - t1) = 0) : a = 0 ∨ t2 = t1 := by
  rcases Int.mul_eq_zero.mp h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by omega)

/-- **Core envelope lemma (ROSA-independent).** The winner set
`{t : (len,ep) of f ≥ that of g}` is convex, i.e. an interval. -/
theorem affine_wins_convex (au bu av bv : Int) :
    ∀ t1 t2 t3 : Int, t1 ≤ t2 → t2 ≤ t3 →
      (au * t1 + bu > 0 ∨ (au * t1 + bu = 0 ∧ av * t1 + bv ≥ 0)) →
      (au * t3 + bu > 0 ∨ (au * t3 + bu = 0 ∧ av * t3 + bv ≥ 0)) →
      (au * t2 + bu > 0 ∨ (au * t2 + bu = 0 ∧ av * t2 + bv ≥ 0)) := by
  intro t1 t2 t3 h12 h23 h1 h3
  have hU1 : 0 ≤ au * t1 + bu := by rcases h1 with h | ⟨h, _⟩ <;> omega
  have hU3 : 0 ≤ au * t3 + bu := by rcases h3 with h | ⟨h, _⟩ <;> omega
  by_cases hle0 : au ≤ 0
  · -- `Δ_L` antitone: `U2 ≥ U3 ≥ 0`
    have hle : au * t3 + bu ≤ au * t2 + bu := aff_anti au bu hle0 h23
    have hU2 : 0 ≤ au * t2 + bu := by omega
    by_cases hp : 0 < au * t2 + bu
    · exact Or.inl hp
    · have hU2z : au * t2 + bu = 0 := by omega
      refine Or.inr ⟨hU2z, ?_⟩
      by_cases h23e : t2 = t3
      · subst h23e
        rcases h3 with h | ⟨_, h⟩ <;> omega
      · have h23lt : t2 < t3 := by omega
        have hU3z : au * t3 + bu = 0 := by omega
        have hau0 : au = 0 := by
          have hs := aff_sub au bu t3 t2
          have hz : au * (t2 - t3) = 0 := by omega
          rcases aff_mul_eq_zero hz with h0 | h0
          · exact h0
          · omega
        have hA1 : au * t1 = 0 := by rw [hau0]; simp
        have hA2 : au * t2 = 0 := by rw [hau0]; simp
        have hV1 : 0 ≤ av * t1 + bv := by rcases h1 with h | ⟨_, h⟩ <;> omega
        have hV3 : 0 ≤ av * t3 + bv := by rcases h3 with h | ⟨_, h⟩ <;> omega
        have hmin := aff_min_le av bv t1 t2 t3 h12 h23
        omega
  · -- `Δ_L` monotone: `U2 ≥ U1 ≥ 0`
    have ha' : 0 ≤ au := by omega
    have hle : au * t1 + bu ≤ au * t2 + bu := aff_mono au bu ha' h12
    have hU2 : 0 ≤ au * t2 + bu := by omega
    by_cases hp : 0 < au * t2 + bu
    · exact Or.inl hp
    · have hU2z : au * t2 + bu = 0 := by omega
      refine Or.inr ⟨hU2z, ?_⟩
      by_cases h12e : t1 = t2
      · subst h12e
        rcases h1 with h | ⟨_, h⟩ <;> omega
      · have h12lt : t1 < t2 := by omega
        have hU1z : au * t1 + bu = 0 := by omega
        have hs := aff_sub au bu t1 t2
        have hz : au * (t2 - t1) = 0 := by omega
        rcases aff_mul_eq_zero hz with h0 | h0
        · omega
        · omega

/-! ### Affine routes -/

/-- An affine route: both coordinates are affine in the position `t`. -/
structure AffRoute where
  aL : Int
  bL : Int
  aE : Int
  bE : Int
  deriving DecidableEq, Repr

namespace AffRoute

def len (f : AffRoute) (t : Int) : Int := f.aL * t + f.bL
def ep (f : AffRoute) (t : Int) : Int := f.aE * t + f.bE

/-- ROSA priority: max `(len, endpoint)` lexicographically. -/
def wins (f g : AffRoute) (t : Int) : Prop :=
  f.len t > g.len t ∨ (f.len t = g.len t ∧ f.ep t ≥ g.ep t)

theorem len_diff (f g : AffRoute) (t : Int) :
    f.len t - g.len t = (f.aL - g.aL) * t + (f.bL - g.bL) := by
  unfold len; rw [Int.sub_mul]; omega

theorem ep_diff (f g : AffRoute) (t : Int) :
    f.ep t - g.ep t = (f.aE - g.aE) * t + (f.bE - g.bE) := by
  unfold ep; rw [Int.sub_mul]; omega

theorem wins_iff (f g : AffRoute) (t : Int) :
    f.wins g t ↔
      ((f.aL - g.aL) * t + (f.bL - g.bL) > 0 ∨
       ((f.aL - g.aL) * t + (f.bL - g.bL) = 0 ∧ (f.aE - g.aE) * t + (f.bE - g.bE) ≥ 0)) := by
  have hL := len_diff f g t
  have hE := ep_diff f g t
  unfold wins
  constructor
  · rintro (h | ⟨h, h'⟩)
    · left; omega
    · right; exact ⟨by omega, by omega⟩
  · rintro (h | ⟨h, h'⟩)
    · left; omega
    · right; exact ⟨by omega, by omega⟩

/-- `E1`/`OwnerEnvelope` core: the winner set of two affine routes is an interval. -/
theorem wins_convex (f g : AffRoute) :
    ∀ t1 t2 t3 : Int, t1 ≤ t2 → t2 ≤ t3 → f.wins g t1 → f.wins g t3 → f.wins g t2 := by
  intro t1 t2 t3 h12 h23 h1 h3
  rw [wins_iff] at h1 h3 ⊢
  exact affine_wins_convex (f.aL - g.aL) (f.bL - g.bL) (f.aE - g.aE) (f.bE - g.bE)
    t1 t2 t3 h12 h23 h1 h3

/-- Interval-restricted form: on `[lo,hi]` the winner set is convex. -/
theorem wins_interval (f g : AffRoute) (lo hi : Int) :
    ∀ t1 t2 t3 : Int, lo ≤ t1 → t1 ≤ t2 → t2 ≤ t3 → t3 ≤ hi →
      f.wins g t1 → f.wins g t3 → f.wins g t2 := by
  intro t1 t2 t3 _ h12 h23 _ h1 h3
  exact wins_convex f g t1 t2 t3 h12 h23 h1 h3


/-- **Finite candidate templates ⇒ `O(1)` owner envelope.**  For any finite list
of affine routes, the set where `f` is the (lex) argmax is an intersection of
intervals, hence itself an interval: the upper envelope has at most one piece
per candidate. -/
theorem wins_list_convex (f : AffRoute) (L : List AffRoute) :
    ∀ t1 t2 t3 : Int, t1 ≤ t2 → t2 ≤ t3 →
      (∀ g ∈ L, f.wins g t1) → (∀ g ∈ L, f.wins g t3) → (∀ g ∈ L, f.wins g t2) := by
  intro t1 t2 t3 h12 h23 h1 h3 g hg
  exact wins_convex f g t1 t2 t3 h12 h23 (h1 g hg) (h3 g hg)

/-! ### ROSA route templates (all affine)

The templates that occur inside one one-bit run pair — `constant`, `slope +1`,
`slope -1`, `RSP` pieces, `single spike`, `bounded affine segment` — are all
instances of `AffRoute`; by `wins_list_convex` their pairwise envelopes compose. -/

/-- Constant route `(v, w)` — e.g. a single spike. -/
def tmplConst (v w : Int) : AffRoute := ⟨0, v, 0, w⟩
/-- Slope-`+1` route (both coordinates `t + c`) — e.g. a repair bridge. -/
def tmplSlopeUp (bL bE : Int) : AffRoute := ⟨1, bL, 1, bE⟩
/-- Plateau-style route: `len` constant, `endpoint` slope `+1`. -/
def tmplPlateau (v bE : Int) : AffRoute := ⟨0, v, 1, bE⟩
/-- Ramp-style route: `len` slope `+1`, `endpoint` constant. -/
def tmplRamp (bL w : Int) : AffRoute := ⟨1, bL, 0, w⟩

end AffRoute
end AffEnv

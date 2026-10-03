import Std
import RosBridge

/-!
## Phase H (new) — step 3: common-birth (expiry) skyline

Abstract, ROSA-free core for the **Q-side**: all candidates share one birth `p`
and only expire.  Each candidate is just `(priority, expiry)` with a total
priority order (smaller = better).  Then `b` wins exactly on
`[max(p, M_b+1), e_b]` where `M_b` is the largest expiry among strictly-better
candidates — the Q-suffix interval `I_Q(b)`.
-/

namespace CommonBirth

open RosBridge

/-- A common-birth candidate: normalised priority and expiry. -/
structure CBCand where
  pr : Int × Int
  e : Nat
  deriving DecidableEq, Repr

/-- Strict `κ` order. -/
def klexLT (x y : Int × Int) : Prop := klexLE x y ∧ x ≠ y

instance (x y : Int × Int) : Decidable (klexLT x y) := by unfold klexLT; infer_instance

/-- `f_b = max(p, M_b + 1)`: the first time `b` can win. -/
def cbF (p : Nat) (cs : List CBCand) (b : CBCand) : Nat :=
  (cs.filter (fun c => decide (klexLT c.pr b.pr))).foldr (fun c acc => max (c.e + 1) acc) p

/-- `b` wins at `t`: active, and every strictly-better candidate has expired. -/
def cbWins (p : Nat) (cs : List CBCand) (b : CBCand) (t : Nat) : Prop :=
  p ≤ t ∧ t ≤ b.e ∧ ∀ c ∈ cs, klexLT c.pr b.pr → c.e < t

theorem le_foldr_cb {l : List CBCand} {x : CBCand} {c : Nat} (h : x ∈ l) :
    x.e + 1 ≤ l.foldr (fun c acc => max (c.e + 1) acc) c := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hh
    · exact Nat.le_trans (Nat.le_refl _) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ih hh) (Nat.le_max_right _ _)

theorem foldr_cb_le (l : List CBCand) (p t : Nat) (hp : p ≤ t) (h : ∀ x ∈ l, x.e + 1 ≤ t) :
    l.foldr (fun c acc => max (c.e + 1) acc) p ≤ t := by
  induction l with
  | nil => exact hp
  | cons y ys ih =>
    rw [List.foldr_cons]
    have h1 : y.e + 1 ≤ t := h y (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

theorem le_foldr_cb_seed (l : List CBCand) (c : Nat) :
    c ≤ l.foldr (fun c acc => max (c.e + 1) acc) c := by
  induction l with
  | nil => exact Nat.le_refl c
  | cons y ys ih => rw [List.foldr_cons]; omega

/-- **Common-birth skyline theorem (Q-suffix).**  The winner set of `b` is exactly
`[max(p, M_b+1), e_b]` (empty when the lower bound exceeds `e_b`). -/
theorem common_birth_winner_iff (p : Nat) (cs : List CBCand) (b : CBCand) (t : Nat) :
    cbWins p cs b t ↔ cbF p cs b ≤ t ∧ t ≤ b.e := by
  constructor
  · rintro ⟨hp, ht, hblk⟩
    refine ⟨?_, ht⟩
    unfold cbF
    apply foldr_cb_le
    · exact hp
    · intro x hx
      rw [List.mem_filter] at hx
      obtain ⟨hc, hp'⟩ := hx
      simp only [decide_eq_true_eq] at hp'
      have : x.e < t := hblk x hc hp'
      omega
  · rintro ⟨hf, ht⟩
    unfold cbF at hf
    have hseed : p ≤ (cs.filter (fun c => decide (klexLT c.pr b.pr))).foldr
        (fun c acc => max (c.e + 1) acc) p := le_foldr_cb_seed _ _
    refine ⟨by omega, ht, ?_⟩
    intro c hc hbetter
    have hmem : c ∈ cs.filter (fun c => decide (klexLT c.pr b.pr)) := by
      rw [List.mem_filter]; exact ⟨hc, by simp [hbetter]⟩
    have := le_foldr_cb (c := p) hmem
    omega

end CommonBirth

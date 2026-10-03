import Std
import Lcs
import RunRectangle

/-!
## Phase D — run capacity records (§7.1)

For a fixed `α=β` rectangle, `run_capacity_reaches` characterises exactly which
endpoints `e ∈ [c,d]` reach a length threshold `λ`: the ramp (`y<x`), the spike
(`y=x`) or the plateau (`x<y`).  This is the semantic core of the two capacity
records `(C₁,E₁)` / `(C₂,E₂)`.
-/

open Lcs RunRect

namespace Capacity

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α]

theorem run_capacity_reaches {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b) (he : c ≤ e) (hed : e ≤ d) {lam : Nat} :
    (lam ≤ lcsLen q k t e) ↔
      ((e - c + 1 < t - a + 1 ∧ lam ≤ e - c + 1) ∨
       (e - c + 1 = t - a + 1 ∧ lam ≤ (t - a + 1) + lcsLen q k (a - 1) (c - 1)) ∨
       (t - a + 1 < e - c + 1 ∧ lam ≤ t - a + 1)) := by
  rw [run_rectangle_rsp hQ hK heq ha hc ht htb he hed]
  by_cases h1 : e - c + 1 < t - a + 1
  · rw [if_pos h1]
    constructor
    · intro h; exact Or.inl ⟨h1, h⟩
    · rintro (⟨_, h⟩ | ⟨h2, _⟩ | ⟨h3, _⟩)
      · exact h
      · omega
      · omega
  · rw [if_neg h1]
    by_cases h2 : e - c + 1 = t - a + 1
    · rw [if_pos h2]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨h2, h⟩)
      · rintro (⟨h1', _⟩ | ⟨_, h⟩ | ⟨h3, _⟩)
        · omega
        · exact h
        · omega
    · rw [if_neg h2]
      constructor
      · intro h; exact Or.inr (Or.inr ⟨by omega, h⟩)
      · rintro (⟨h1', _⟩ | ⟨h2', _⟩ | ⟨_, h⟩)
        · omega
        · omega
        · exact h

/-- §7.1 run capacity records: the latest endpoint reaching `λ`.
Three-way: the last endpoint `d` reaches when `λ ≤ min(x, n)`; otherwise the spike
endpoint `c+x-1` reaches when `x ≤ n` and `λ ≤ x+γ`; otherwise no endpoint in
`[c,d]` reaches `λ`. -/
theorem run_capacity_latest_endpoint {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    (ha : 0 < a) (hc : 0 < c) (hcd : c ≤ d)
    {t : Nat} (ht : a ≤ t) (htb : t ≤ b) {lam : Nat} :
    (lam ≤ min (t - a + 1) (d - c + 1) → lam ≤ lcsLen q k t d)
    ∧ (min (t - a + 1) (d - c + 1) < lam → t - a + 1 ≤ d - c + 1 →
        lam ≤ (t - a + 1) + lcsLen q k (a - 1) (c - 1) →
        lam ≤ lcsLen q k t (c + (t - a + 1) - 1))
    ∧ (min (t - a + 1) (d - c + 1) < lam →
        (d - c + 1 < t - a + 1 ∨ (t - a + 1) + lcsLen q k (a - 1) (c - 1) < lam) →
        ∀ e, c ≤ e → e ≤ d → ¬ (lam ≤ lcsLen q k t e)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hlam
    have hmem := run_capacity_reaches (t := t) (e := d) hQ hK heq ha hc ht htb
      hcd (Nat.le_refl d) (lam := lam)
    rcases Nat.lt_trichotomy (d - c + 1) (t - a + 1) with hlt | heq' | hgt
    · exact hmem.mpr (Or.inl ⟨hlt, by omega⟩)
    · exact hmem.mpr (Or.inr (Or.inl ⟨heq', by omega⟩))
    · exact hmem.mpr (Or.inr (Or.inr ⟨hgt, by omega⟩))
  · intro hgt hxn hspike
    have hmem := run_capacity_reaches (t := t) (e := c + (t - a + 1) - 1) hQ hK heq ha hc
      ht htb (by omega) (by omega) (lam := lam)
    exact hmem.mpr (Or.inr (Or.inl ⟨by omega, hspike⟩))
  · intro hgt hdisj e hce hed hle
    have hmem := run_capacity_reaches (t := t) (e := e) hQ hK heq ha hc ht htb hce hed
      (lam := lam)
    rcases hmem.mp hle with ⟨hy1, hlam1⟩ | ⟨hy2, hlam2⟩ | ⟨hy3, hlam3⟩
    · omega
    · omega
    · omega

end Capacity

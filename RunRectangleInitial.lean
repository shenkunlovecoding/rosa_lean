import Repair

/-!
## Initial run pairs and the guarded gamma recurrence

`RunRect.run_rectangle_offset_eq` and `RunRect.run_rectangle_rsp` require both
runs to have a nonempty diagonal predecessor (`0 < a` and `0 < c`).  This file
adds their zero-predecessor base case and combines both cases using
`Repair.leftCtx`, whose value is definitionally `0` on the initial-run boundary.
The resulting run-grid recurrence has no positivity side conditions.
-/

open Lcs RunRect

set_option linter.unusedSectionVars false

namespace RunRectInitial

variable {α : Type} [DecidableEq α]

/-- Equal-offset LCS rectangle formula when either run starts at the beginning
of its string.  In this case the diagonal predecessor is empty and the whole
matching suffix lies inside the current run pair. -/
theorem run_rectangle_offset_eq_base
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (heq : αs = βs) (hbase : a = 0 ∨ c = 0)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b)
    (he : c ≤ e) (hed : e ≤ d) (hxy : t - a = e - c) :
    lcsLen q k t e = t - a + 1 := by
  rcases hbase with ha | hc
  · subst a
    apply lcsLen_eq_of
    · refine ⟨by omega, by omega, ?_⟩
      intro h hh
      rw [List.mem_range] at hh
      have hqt : q (t - h) = αs := hQ.mem (t - h) (by omega) (by omega)
      have hke : k (e - h) = βs := hK.mem (e - h) (by omega) (by omega)
      rw [hqt, hke, heq]
    · intro hcon
      have := hcon.1
      omega
  · subst c
    apply lcsLen_eq_of
    · refine ⟨by omega, by omega, ?_⟩
      intro h hh
      rw [List.mem_range] at hh
      have hqt : q (t - h) = αs := hQ.mem (t - h) (by omega) (by omega)
      have hke : k (e - h) = βs := hK.mem (e - h) (by omega) (by omega)
      rw [hqt, hke, heq]
    · intro hcon
      have := hcon.2.1
      omega

/-- The equal-offset rectangle formula with the predecessor value guarded by
`Repair.leftCtx`.  This is the pointed/initial-run analogue of
`RunRect.run_rectangle_offset_eq`. -/
theorem run_rectangle_offset_eq_leftCtx
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs)
    (heq : αs = βs) {t e : Nat}
    (ht : a ≤ t) (htb : t ≤ b) (he : c ≤ e) (hed : e ≤ d)
    (hxy : t - a = e - c) :
    lcsLen q k t e = (t - a + 1) + Repair.leftCtx q k a c := by
  by_cases ha : 0 < a
  · by_cases hc : 0 < c
    · rw [Repair.leftCtx_eq (q := q) (k := k) ha hc]
      exact RunRect.run_rectangle_offset_eq hQ hK heq ha hc ht htb he hed hxy
    · have hbase : a = 0 ∨ c = 0 := Or.inr (by omega)
      rw [Repair.leftCtx_zero (q := q) (k := k) hbase, Nat.add_zero]
      exact run_rectangle_offset_eq_base hQ hK heq hbase ht htb he hed hxy
  · have hbase : a = 0 ∨ c = 0 := Or.inl (by omega)
    rw [Repair.leftCtx_zero (q := q) (k := k) hbase, Nat.add_zero]
    exact run_rectangle_offset_eq_base hQ hK heq hbase ht htb he hed hxy

/-- RSP row shape for a same-symbol run rectangle, including the initial-run
cases.  The spike recurses through `Repair.leftCtx`, so it is exactly `x + 0`
when either diagonal predecessor is empty. -/
theorem run_rectangle_rsp_leftCtx
    {q k : Nat → α} {Tq Tk a b c d : Nat} {αs βs : α}
    (hQ : ConstRun q Tq a b αs) (hK : ConstRun k Tk c d βs) (heq : αs = βs)
    {t e : Nat} (ht : a ≤ t) (htb : t ≤ b) (he : c ≤ e) (hed : e ≤ d) :
    lcsLen q k t e =
      (if e - c + 1 < t - a + 1 then e - c + 1
       else if e - c + 1 = t - a + 1 then
         (t - a + 1) + Repair.leftCtx q k a c
       else t - a + 1) := by
  by_cases h1 : e - c + 1 < t - a + 1
  · rw [if_pos h1]
    exact run_rectangle_offset_gt hQ hK heq ht htb he hed (by omega)
  · rw [if_neg h1]
    by_cases h2 : e - c + 1 = t - a + 1
    · rw [if_pos h2]
      exact run_rectangle_offset_eq_leftCtx hQ hK heq ht htb he hed (by omega)
    · rw [if_neg h2]
      exact run_rectangle_offset_lt hQ hK heq ht htb he hed (by omega)

/-- Unified run-grid gamma recurrence.  This is `RunRect.run_grid_gamma_recurrence`
with both positivity hypotheses removed; the recursive predecessor becomes
`Repair.leftCtx q k ap cp`. -/
theorem run_grid_gamma_recurrence_leftCtx
    {q k : Nat → α} {Tq Tk ap bp cp dp : Nat} {αp βp : α}
    (hQp : ConstRun q Tq ap bp αp) (hKp : ConstRun k Tk cp dp βp)
    (hapb : ap ≤ bp) (hcpd : cp ≤ dp) :
    lcsLen q k bp dp =
      (if αp = βp then
        (if dp - cp + 1 < bp - ap + 1 then dp - cp + 1
         else if dp - cp + 1 = bp - ap + 1 then
           (bp - ap + 1) + Repair.leftCtx q k ap cp
         else bp - ap + 1)
       else 0) := by
  by_cases heq : αp = βp
  · rw [if_pos heq]
    exact run_rectangle_rsp_leftCtx hQp hKp heq hapb (Nat.le_refl bp)
      hcpd (Nat.le_refl dp)
  · rw [if_neg heq]
    exact run_rectangle_symbol_ne hQp hKp heq hapb (Nat.le_refl bp)
      hcpd (Nat.le_refl dp)

end RunRectInitial

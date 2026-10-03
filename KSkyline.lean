import Std
import RosBridge
import CommonBirth
import KDeleteAbstract

/-!
## Phase H (new) — step 8: abstract K-suffix skyline (`KSkyline`)

Assembling step 6 (`HasPrebirthShadow`) and step 7 (`TrimClosed`) with the
parametric deletion threshold `d`: the K-side winner of a bridge `b` is exactly
`[max(p, d, M_b+1), e_b]`, where `M_b` is the last expiry of a strictly-better
same-owner bridge.  Still string-free — the ROSA refinement is what discharges
`HasPrebirthShadow` / `TrimClosed`.
-/

namespace KSkyline
open Route RosBridge CommonBirth KDeleteAbstract

/-- **step 8 — K-suffix winner interval.**  With `D` trim-closed, pre-birth shadow
for every strictly-better same-owner bridge whose shadow reaches back to `p`, and
`d` the deletion first-win threshold, `b` is the K-side winner exactly on
`[max(p, d, M+1), e_b]`. -/
theorem k_suffix_winner_iff {D : KDeleteFamily} {others : List Bridge} {b : Bridge}
    (htrim : TrimClosed D)
    (hshadow : ∀ c ∈ others, klexLT c.kappa b.kappa → HasPrebirthShadow D c)
    (hreach : ∀ c ∈ others, klexLT c.kappa b.kappa → c.shadowStart ≤ (b.p : Int))
    {d : Nat} (hdlow : ∀ t, b.p ≤ t → t < d → ¬ D.Beats b t)
    (hdhigh : ∀ t, d ≤ t → t ≤ b.death → D.Beats b t)
    {M : Nat} (hM : ∀ c ∈ others, klexLT c.kappa b.kappa → c.death ≤ M)
    (hMat : M < b.p ∨ ∃ c ∈ others, klexLT c.kappa b.kappa ∧ c.death = M) :
    ∀ t, (b.Active t ∧ D.Beats b t ∧ ∀ c ∈ others, c.Active t → ¬ klexLT c.kappa b.kappa)
      ↔ max b.p (max d (M + 1)) ≤ t ∧ t ≤ b.death := by
  intro t
  constructor
  · rintro ⟨hact, hbeats, hno⟩
    have hpb : b.p ≤ t := hact.1
    have hte : t ≤ b.death := hact.2
    have hd : d ≤ t := by
      by_cases h : t < d
      · exact absurd hbeats (hdlow t hpb h)
      · omega
    have hMt : M < t := by
      by_cases h : M < t
      · exact h
      · exfalso
        rcases hMat with hmp | ⟨c, hc, hbetter, hcM⟩
        · omega
        · have hcd : c.death ≤ M := hM c hc hbetter
          have htc : t ≤ c.death := by omega
          by_cases hcb : c.birth ≤ t
          · exact hno c hc ⟨hcb, htc⟩ hbetter
          · have hcs : c.shadowStart ≤ (t : Int) := by
              have := hreach c hc hbetter
              omega
            exact shadow_not_beats (hshadow c hc hbetter) hbetter hact hcs (by omega) hbeats
    omega
  · rintro ⟨hmax, hte⟩
    have hp : b.p ≤ t := Nat.le_trans (Nat.le_max_left b.p (max d (M + 1))) hmax
    have hd : d ≤ t :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left d (M + 1)) (Nat.le_max_right b.p (max d (M + 1)))) hmax
    have hM1 : M + 1 ≤ t :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right d (M + 1)) (Nat.le_max_right b.p (max d (M + 1)))) hmax
    refine ⟨⟨hp, hte⟩, hdhigh t hd hte, ?_⟩
    intro c hc hca hbetter
    have hcd : c.death ≤ M := hM c hc hbetter
    have htc : t ≤ c.death := hca.2
    omega

end KSkyline

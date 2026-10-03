import Std
import RosBridge
import CommonBirth

/-!
## Phase H (new) — step 8 (parametric ceiling, §14)

The guide's §14 advises proving the K-suffix theorem in a **parametric** form
first: assume a deletion first-win threshold `d` and the last expiry `M` of
strictly-better same-owner candidates, and derive the winner interval.  Steps 6–7
(pre-birth shadow, Trim-closure) are what *construct* `d`; the extremum-extraction
wrapper comes later.
-/

namespace KSuffix

/-- **K-side suffix ceiling.**  A bridge `b` (birth `p`, expiry `e`) that beats the
deletion baseline exactly from `d` on, with `M` the last expiry of strictly-better
same-owner candidates, is the final K-side winner exactly on
`[max(p, d, M+1), e]`. -/
theorem k_suffix_ceiling {p e d M : Nat} (beats : Nat → Prop)
    (hlow : ∀ t, p ≤ t → t < d → ¬ beats t)
    (hhigh : ∀ t, d ≤ t → t ≤ e → beats t) :
    ∀ t, (p ≤ t ∧ t ≤ e ∧ beats t ∧ M < t) ↔ max p (max d (M + 1)) ≤ t ∧ t ≤ e := by
  intro t
  constructor
  · rintro ⟨hp, ht, hb, hM⟩
    have hd : d ≤ t := by
      by_cases h : t < d
      · exact absurd hb (hlow t hp h)
      · omega
    omega
  · rintro ⟨hmax, ht⟩
    exact ⟨by omega, ht, hhigh t (by omega) ht, by omega⟩

end KSuffix

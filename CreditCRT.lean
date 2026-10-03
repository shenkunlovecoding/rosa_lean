import Std

/-!
## Exact ROSA credit — §5 of `ROSA_Credit_New_Results` (exactness of the CRT backend)

The prototype recovers each signed integer answer from its residues modulo the
NTT primes.  With `H_g = Σ_{t,j} |g_{t,j}|` and binary `V`, both the exact value
and every block sum have absolute value at most `H_g`, so choosing the modulus
**product** `P > 2·H_g` lets the CRT result be read back uniquely as the centred
representative.

This file proves exactly that uniqueness statement:

* `crt_unique` — two integers of absolute value `< P/2` that agree modulo `P`
  (in `Int` `%`-sense) are equal;
* `crt_unique_three` — the three-modulus product instance used by the prototype
  (`modulus_product > 2 * bound`).
-/

namespace CreditCRT

/-- **§5, CRT uniqueness.**  If `2·|x| < P`, `2·|y| < P` and `x ≡ y (mod P)` then
`x = y`; hence a signed value is recovered uniquely from its residue modulo a
product that exceeds twice the absolute bound.  (`P > 0` is part of the interface
— it is what makes the residue a faithful encoding of the prototype; the statement
itself also holds for `P = 0`.) -/
theorem crt_unique {P : Nat} (_hP : 0 < P) {x y : Int}
    (hx : 2 * x.natAbs < P) (hy : 2 * y.natAbs < P)
    (h : x % (P : Int) = y % (P : Int)) : x = y := by
  by_cases hne : x = y
  · exact hne
  · exfalso
    have hmod : (x - y) % (P : Int) = 0 := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp h
    have hdiv : (P : Int) ∣ (x - y) := Int.dvd_of_emod_eq_zero hmod
    obtain ⟨k, hk⟩ := hdiv
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, Int.mul_zero] at hk
      exact hne (by omega)
    have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
    have h2 : (x - y).natAbs = P * k.natAbs := by
      rw [hk, Int.natAbs_mul]
      simp
    have h3 : (x - y).natAbs ≤ x.natAbs + y.natAbs := Int.natAbs_sub_le x y
    have h4 : x.natAbs + y.natAbs < P := by omega
    have h5 : P ≤ P * k.natAbs := by
      have := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hkpos)
      simpa using this
    omega

/-- **§5, three-modulus instance.**  The prototype's `modulus_product` is the
product of up to three NTT primes; whenever that product exceeds `2·H_g` the CRT
recovery of any value bounded by `H_g` is exact. -/
theorem crt_unique_three (p₁ p₂ p₃ Hg : Nat) {x y : Int}
    (hP : 0 < p₁ * p₂ * p₃)
    (hx : 2 * x.natAbs ≤ Hg) (hy : 2 * y.natAbs ≤ Hg)
    (hHg : 2 * Hg < p₁ * p₂ * p₃)
    (hres : x % ((p₁ * p₂ * p₃ : Nat) : Int) = y % ((p₁ * p₂ * p₃ : Nat) : Int)) :
    x = y :=
  crt_unique hP (by omega) (by omega) hres

/-- **§5, absolute bound is enough.**  For a value with `|x| ≤ H_g` and a modulus
product `P > 2·H_g` the hypothesis `2·|x| < P` of `crt_unique` holds. -/
theorem two_natAbs_lt_of_le {P Hg : Nat} {x : Int} (hx : x.natAbs ≤ Hg) (h : 2 * Hg < P) :
    2 * x.natAbs < P := by omega

end CreditCRT

import Atlas.OrderArithmetic.Positivity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

namespace Atlas.OrderArithmetic

/-- Equal orders in a common characteristic have equal characteristic exponents. -/
theorem equal_order_exponents {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) :
    f * characteristicExponent x = g * characteristicExponent y := by
  rw [← order_characteristic_valuation hx hlx hp hf hqx,
    ← order_characteristic_valuation hy hly hp hg hqy, he]

/-- Positive solutions of A*f=B*g have one common positive parameter. -/
theorem proportional_exponents {A B f g : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hf : 0 < f) (he : A * f = B * g) :
    ∃ t : ℕ, 1 ≤ t ∧ f = (B / Nat.gcd A B) * t ∧ g = (A / Nat.gcd A B) * t := by
  let c := Nat.gcd A B
  have hc : 0 < c := Nat.gcd_pos_of_pos_left B hA
  have hAc : A / c * c = A := Nat.div_mul_cancel (Nat.gcd_dvd_left A B)
  have hBc : B / c * c = B := Nat.div_mul_cancel (Nat.gcd_dvd_right A B)
  have hred : (A / c) * f = (B / c) * g := by nlinarith
  have hcop : Nat.Coprime (A / c) (B / c) := Nat.coprime_div_gcd_div_gcd hc
  have hd : B / c ∣ f := hcop.symm.dvd_of_dvd_mul_left ⟨g, hred⟩
  obtain ⟨t, ht⟩ := hd
  have htpos : 1 ≤ t := by
    by_contra h
    have hz : t = 0 := by omega
    simp [hz] at ht
    omega
  have hBq : 0 < B / c := by nlinarith
  refine ⟨t, htpos, ht, ?_⟩
  rw [ht] at hred
  nlinarith

/-- The two field sizes become integer powers of a single integer z≥2. -/
theorem equal_order_common_parameter {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) :
    ∃ t z : ℕ, 1 ≤ t ∧ 2 ≤ z ∧ z = p ^ t ∧
      fieldSize x = z ^ (characteristicExponent y /
        Nat.gcd (characteristicExponent x) (characteristicExponent y)) ∧
      fieldSize y = z ^ (characteristicExponent x /
        Nat.gcd (characteristicExponent x) (characteristicExponent y)) := by
  have ha := characteristicExponent_pos hx hlx
  have hb := characteristicExponent_pos hy hly
  have hval := equal_order_exponents hx hy hlx hly hp hf hg hqx hqy he
  obtain ⟨t, ht, hft, hgt⟩ := proportional_exponents (by omega : 0 < characteristicExponent x)
    (by omega : 0 < characteristicExponent y) (by omega : 0 < f)
    (by simpa [mul_comm] using hval)
  refine ⟨t, p ^ t, ht, hp.two_le.trans (Nat.le_pow (by omega)), rfl, ?_, ?_⟩
  · rw [hqx, hft, ← pow_mul, mul_comm t]
  · rw [hqy, hgt, ← pow_mul, mul_comm t]

/-- Cancel the common characteristic contribution and clear exact central divisors. -/
theorem equal_order_residual_cross {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) :
    denominator y * residual x = denominator x * residual y := by
  have hv := equal_order_exponents hx hy hlx hly hp hf hg hqx hqy he
  have hpow : fieldSize x ^ characteristicExponent x =
      fieldSize y ^ characteristicExponent y := by rw [hqx, hqy, ← pow_mul, ← pow_mul, hv]
  rw [lie_order_eq hlx, lie_order_eq hly, numerator, numerator,
    quotient_factorization (denominator_dvd_residual hx),
    quotient_factorization (denominator_dvd_residual hy), hpow] at he
  have hpos : 0 < fieldSize y ^ characteristicExponent y :=
    pow_pos (by have := primePower_two_le (lie_field_primePower hy hly); omega) _
  have hquot := Nat.eq_of_mul_eq_mul_left hpos he
  have hex := Nat.div_mul_cancel (denominator_dvd_residual hx)
  have hey := Nat.div_mul_cancel (denominator_dvd_residual hy)
  calc
    denominator y * residual x = denominator y * ((residual x / denominator x) * denominator x) := by rw [hex]
    _ = denominator x * ((residual y / denominator y) * denominator y) := by rw [hquot]; ring
    _ = denominator x * residual y := by rw [hey]

end Atlas.OrderArithmetic

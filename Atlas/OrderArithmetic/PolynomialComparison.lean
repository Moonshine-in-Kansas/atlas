import Atlas.OrderArithmetic.ClassicalCollision
import Atlas.OrderArithmetic.ResidualPolynomial
import Atlas.OrderArithmetic.PolynomialDenominators

namespace Atlas.OrderArithmetic
open Polynomial

/-- Identical family/rank templates cannot give two field sizes of equal order
in a common characteristic. -/
theorem same_template_equal_order_eq {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (ht : withField x 0 = withField y 0) : x = y := by
  have ha : characteristicExponent x = characteristicExponent y := by
    simpa only [characteristicExponent_withField] using congrArg characteristicExponent ht
  have hq := field_eq_of_equal_order_and_exponent hx hy hlx hly hp hf hg hqx hqy he ha
  calc
    x = withField (withField x 0) (fieldSize x) := by simp
    _ = withField (withField y 0) (fieldSize y) := by rw [ht, hq]
    _ = y := by simp

/-- A checked coefficient certificate gives a complete finite set of possible
positive common parameters; no arbitrary field-size cutoff enters. -/
theorem comparison_parameter_mem_divisors {x y : RawEntry} {z a b k : ℕ}
    {c : ℤ} {R : ℤ[X]} (hx : Admissible x) (hy : Admissible y)
    (hlx : IsLie x) (hly : IsLie y) (hz : 2 ≤ z) (hc : c ≠ 0)
    (hqx : fieldSize x = z ^ b) (hqy : fieldSize y = z ^ a)
    (he : denominator y * residual x = denominator x * residual y)
    (hcert : comparisonPolynomial x y b a (denominator x) (denominator y) =
      X ^ k * (C c + X * R)) : z ∈ c.natAbs.divisors := by
  have hd : (z : ℤ) ∣ c := integer_root_dvd_coefficient _ R k c z
    (by exact_mod_cast (show z ≠ 0 by omega)) hcert
    (comparisonPolynomial_eval_zero hx hy hlx hly hqx hqy he)
  apply Nat.mem_divisors.mpr
  exact ⟨by simpa using Int.natAbs_dvd_natAbs.mpr hd, by simpa using hc⟩

end Atlas.OrderArithmetic

import Atlas.OrderArithmetic.ExponentReduction
import Atlas.OrderArithmetic.IntegerRoot
import Mathlib.Algebra.Polynomial.BigOperators

namespace Atlas.OrderArithmetic
open Polynomial
open scoped BigOperators

/-- The actual residual formula as an integer polynomial in the field size.
The field-size coordinate of the label is ignored, while its family and rank
are retained. This is not an assertion of equality of formal polynomials from
equality of their values. -/
noncomputable def residualPolynomial : RawEntry → ℤ[X]
  | .linear d _ => ∏ i ∈ Finset.Icc 2 d, (X ^ i - 1)
  | .unitary d _ => ∏ i ∈ Finset.Icc 2 d, if Even i then X ^ i - 1 else X ^ i + 1
  | .B r _ | .C r _ => ∏ i ∈ Finset.Icc 1 r, (X ^ (2 * i) - 1)
  | .Dplus r _ => (X ^ r - 1) * ∏ i ∈ Finset.Icc 1 (r - 1), (X ^ (2 * i) - 1)
  | .Dminus r _ => (X ^ r + 1) * ∏ i ∈ Finset.Icc 1 (r - 1), (X ^ (2 * i) - 1)
  | .G2 _ => (X ^ 6 - 1) * (X ^ 2 - 1)
  | .F4 _ => ∏ i ∈ ({2, 6, 8, 12} : Finset ℕ), (X ^ i - 1)
  | .E6 _ => ∏ i ∈ ({2, 5, 6, 8, 9, 12} : Finset ℕ), (X ^ i - 1)
  | .E7 _ => ∏ i ∈ ({2, 6, 8, 10, 12, 14, 18} : Finset ℕ), (X ^ i - 1)
  | .E8 _ => ∏ i ∈ ({2, 8, 12, 14, 18, 20, 24, 30} : Finset ℕ), (X ^ i - 1)
  | .twistedE6 _ => (X ^ 12 - 1) * (X ^ 9 + 1) * (X ^ 8 - 1) *
      (X ^ 6 - 1) * (X ^ 5 + 1) * (X ^ 2 - 1)
  | .trialityD4 _ => (X ^ 8 + X ^ 4 + 1) * (X ^ 6 - 1) * (X ^ 2 - 1)
  | .suzuki _ => (X ^ 2 + 1) * (X - 1)
  | .smallRee _ => (X ^ 3 + 1) * (X - 1)
  | .largeRee _ => (X ^ 6 + 1) * (X ^ 4 - 1) * (X ^ 3 + 1) * (X - 1)
  | _ => 1

theorem residualPolynomial_eval {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    (residualPolynomial x).eval (fieldSize x : ℤ) = (residual x : ℤ) := by
  have hq := primePower_two_le (lie_field_primePower hx hl)
  have hc : ∀ i : ℕ, ((fieldSize x ^ i - 1 : ℕ) : ℤ) = (fieldSize x : ℤ) ^ i - 1 := by
    intro i
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | unitary d q =>
    simp only [fieldSize] at hc ⊢
    simp only [residualPolynomial, residual, eval_prod, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases he : Even i
    · simp [he, unitaryFactor, ← hc i]
    · simp [he, unitaryFactor]
  | suzuki q | smallRee q | largeRee q =>
    simp only [fieldSize] at hc ⊢
    have h1 := hc 1
    simp only [pow_one] at h1
    simp [residualPolynomial, residual, fieldSize, h1, hc]
  | _ =>
    simp only [fieldSize] at hc ⊢
    simp [residualPolynomial, residual, eval_prod, hc]

/-- Clear the two central denominators after replacing field sizes by powers of
one integer parameter. The denominator candidates remain explicit. -/
noncomputable def comparisonPolynomial (x y : RawEntry) (b a dx dy : ℕ) : ℤ[X] :=
  C (dy : ℤ) * (residualPolynomial x).comp (X ^ b) -
    C (dx : ℤ) * (residualPolynomial y).comp (X ^ a)

theorem comparisonPolynomial_eval_zero {x y : RawEntry} {z a b : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hqx : fieldSize x = z ^ b) (hqy : fieldSize y = z ^ a)
    (he : denominator y * residual x = denominator x * residual y) :
    (comparisonPolynomial x y b a (denominator x) (denominator y)).eval (z : ℤ) = 0 := by
  simp only [comparisonPolynomial, eval_sub, eval_mul, eval_C, eval_comp, eval_pow, eval_X]
  rw [← Nat.cast_pow, ← Nat.cast_pow, ← hqx, ← hqy,
    residualPolynomial_eval hx hlx, residualPolynomial_eval hy hly]
  exact sub_eq_zero.mpr (by exact_mod_cast he)

theorem equal_order_polynomial_parameter {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) :
    ∃ t z : ℕ, 1 ≤ t ∧ 2 ≤ z ∧ z = p ^ t ∧
      fieldSize x = z ^ (characteristicExponent y /
        Nat.gcd (characteristicExponent x) (characteristicExponent y)) ∧
      fieldSize y = z ^ (characteristicExponent x /
        Nat.gcd (characteristicExponent x) (characteristicExponent y)) ∧
      (comparisonPolynomial x y
        (characteristicExponent y / Nat.gcd (characteristicExponent x) (characteristicExponent y))
        (characteristicExponent x / Nat.gcd (characteristicExponent x) (characteristicExponent y))
        (denominator x) (denominator y)).eval (z : ℤ) = 0 := by
  obtain ⟨t, z, ht, hz, hpz, hxz, hyz⟩ :=
    equal_order_common_parameter hx hy hlx hly hp hf hg hqx hqy he
  exact ⟨t, z, ht, hz, hpz, hxz, hyz, comparisonPolynomial_eval_zero hx hy hlx hly hxz hyz
    (equal_order_residual_cross hx hy hlx hly hp hf hg hqx hqy he)⟩

end Atlas.OrderArithmetic

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-! Natural-number algebra for the two actual weighted F4 parabolic factors.
This module contains no group-order premise. Source only; verification is separate. -/

namespace Atlas.Chevalley.TwistedE6.ClosedOrder

/-- The product of the weighted 24-representative factor and the weighted B3 factor. -/
def weightedWeylPolynomial (q : ℕ) : ℕ :=
  ((1 + q + q ^ 2) * (1 + q ^ 4) * (1 + q ^ 6) * (1 + q ^ 9)) *
    ((1 + q) * (1 + q ^ 2) * (1 + q ^ 3) * (1 + q ^ 2 + q ^ 4) * (1 + q ^ 5))

private theorem natural_geometric_two (x : ℕ) (hx : 1 ≤ x) :
    (x - 1) * (1 + x) = x ^ 2 - 1 := by
  calc
    _ = (∑ i ∈ Finset.range 2, x ^ i) * (x - 1) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
        zero_add]
      exact mul_comm _ _
    _ = _ := geom_sum_mul_of_one_le hx 2

private theorem natural_geometric_three (x : ℕ) (hx : 1 ≤ x) :
    (x - 1) * (1 + x + x ^ 2) = x ^ 3 - 1 := by
  calc
    _ = (∑ i ∈ Finset.range 3, x ^ i) * (x - 1) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
        zero_add]
      exact mul_comm _ _
    _ = _ := geom_sum_mul_of_one_le hx 3

/-- Multiplication by the actual fixed-torus factor gives the six required
factors. The hypothesis handles truncated subtraction in the naturals. -/
theorem weightedWeylPolynomial_torus (q : ℕ) (hq : 1 ≤ q) :
    weightedWeylPolynomial q * ((q - 1) ^ 2 * (q ^ 2 - 1) ^ 2) =
      (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) := by
  have hp (n : ℕ) : 1 ≤ q ^ n := one_le_pow₀ hq
  have h2 : (q - 1) * (1 + q) = q ^ 2 - 1 := natural_geometric_two q hq
  have h4 : (q ^ 2 - 1) * (1 + q ^ 2) = q ^ 4 - 1 := by
    simpa only [← pow_mul] using natural_geometric_two (q ^ 2) (hp 2)
  have h6 : (q - 1) * (1 + q + q ^ 2) * (1 + q ^ 3) = q ^ 6 - 1 := by
    rw [natural_geometric_three q hq]
    simpa only [← pow_mul] using natural_geometric_two (q ^ 3) (hp 3)
  have h8 : (q ^ 2 - 1) * (1 + q ^ 2) * (1 + q ^ 4) = q ^ 8 - 1 := by
    rw [h4]
    simpa only [← pow_mul] using natural_geometric_two (q ^ 4) (hp 4)
  have h6' : (q ^ 2 - 1) * (1 + q ^ 2 + q ^ 4) = q ^ 6 - 1 := by
    simpa only [← pow_mul] using natural_geometric_three (q ^ 2) (hp 2)
  have h12 : (q ^ 2 - 1) * (1 + q ^ 2 + q ^ 4) * (1 + q ^ 6) =
      q ^ 12 - 1 := by
    rw [h6']
    simpa only [← pow_mul] using natural_geometric_two (q ^ 6) (hp 6)
  calc
    _ = ((q ^ 2 - 1) * (1 + q ^ 2 + q ^ 4) * (1 + q ^ 6)) * (1 + q ^ 9) *
        ((q ^ 2 - 1) * (1 + q ^ 2) * (1 + q ^ 4)) *
        ((q - 1) * (1 + q + q ^ 2) * (1 + q ^ 3)) * (1 + q ^ 5) *
        ((q - 1) * (1 + q)) := by
      simp only [weightedWeylPolynomial, pow_two]
      ac_rfl
    _ = _ := by
      rw [h12, h8, h6, h2]
      ac_rfl

/-- The same identity in the exact multiplication order of the fixed Bruhat count. -/
theorem weightedWeylPolynomial_bruhat (q : ℕ) (hq : 1 ≤ q) :
    weightedWeylPolynomial q * (q ^ 36 * (q - 1) ^ 2 * (q ^ 2 - 1) ^ 2) =
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) := by
  calc
    _ = q ^ 36 * (weightedWeylPolynomial q * ((q - 1) ^ 2 * (q ^ 2 - 1) ^ 2)) := by
      ac_rfl
    _ = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)) := by
      rw [weightedWeylPolynomial_torus q hq]
    _ = _ := by ac_rfl

end Atlas.Chevalley.TwistedE6.ClosedOrder

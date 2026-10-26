import Atlas.OrderArithmetic.IntegerRootCoefficient

namespace Atlas.OrderArithmetic
open Polynomial

/-- A checked finite coefficient prefix supplies all possible positive integer
roots, without computing the remaining coefficients. -/
theorem integer_root_mem_prefix_divisors {P : ℤ[X]} {k z : ℕ} {c : ℤ}
    (hz : 2 ≤ z) (hc : c ≠ 0)
    (hprefix : ∀ i ∈ Finset.range (k + 1), P.coeff i = if i = k then c else 0)
    (hroot : P.eval (z : ℤ) = 0) : z ∈ c.natAbs.divisors := by
  have hk : P.coeff k = c := by simpa using hprefix k (Finset.mem_range.mpr (by omega))
  have hlow : ∀ i < k, P.coeff i = 0 := by
    intro i hi
    simpa [show i ≠ k by omega] using hprefix i (Finset.mem_range.mpr (by omega))
  simpa only [hk] using integer_root_mem_first_coefficient_divisors hz (by simpa [hk]) hlow hroot

/-- In particular a first coefficient of absolute value one excludes all
integer roots at least two. -/
theorem integer_eval_ne_zero_of_unit_prefix {P : ℤ[X]} {k z : ℕ} {c : ℤ}
    (hz : 2 ≤ z) (hc : c.natAbs = 1)
    (hprefix : ∀ i ∈ Finset.range (k + 1), P.coeff i = if i = k then c else 0) :
    P.eval (z : ℤ) ≠ 0 := by
  intro hroot
  have hdiv := integer_root_mem_prefix_divisors hz (by intro h; simp [h] at hc) hprefix hroot
  rw [hc] at hdiv
  have hd := (Nat.mem_divisors.mp hdiv).1
  have := Nat.le_of_dvd (by decide : 0 < 1) hd
  omega

end Atlas.OrderArithmetic

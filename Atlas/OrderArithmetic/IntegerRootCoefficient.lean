import Atlas.OrderArithmetic.IntegerRoot
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Divisors

namespace Atlas.OrderArithmetic
open Polynomial

/-- A coefficient certificate can be checked without expanding the entire
polynomial: every coefficient below k is zero. -/
theorem integer_root_dvd_first_coefficient {P : ℤ[X]} {k : ℕ} {z : ℤ}
    (hz : z ≠ 0) (hlow : ∀ i < k, P.coeff i = 0) (hroot : P.eval z = 0) :
    z ∣ P.coeff k := by
  obtain ⟨Q, hQ⟩ := X_pow_dvd_iff.mpr hlow
  have hQr : Q.eval z = 0 := by
    rw [hQ, eval_mul, eval_pow, eval_X] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hz)
  have hcoeff : P.coeff k = Q.coeff 0 := by
    rw [hQ]
    simpa using coeff_X_pow_mul Q k 0
  rw [hcoeff]
  exact IsRoot.dvd_coeff_zero hQr

theorem integer_root_mem_first_coefficient_divisors {P : ℤ[X]} {k z : ℕ}
    (hz : 2 ≤ z) (hc : P.coeff k ≠ 0)
    (hlow : ∀ i < k, P.coeff i = 0) (hroot : P.eval (z : ℤ) = 0) :
    z ∈ (P.coeff k).natAbs.divisors := by
  have hd := integer_root_dvd_first_coefficient
    (by exact_mod_cast (show z ≠ 0 by omega)) hlow hroot
  exact Nat.mem_divisors.mpr
    ⟨by simpa using Int.natAbs_dvd_natAbs.mpr hd, by simpa using hc⟩

end Atlas.OrderArithmetic

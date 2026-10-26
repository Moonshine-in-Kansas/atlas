import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

namespace Atlas.OrderArithmetic
open Polynomial

/-- A certificate with its lowest nonzero coefficient exposed bounds every nonzero
integer root by divisibility. No numerical search cutoff is assumed. -/
theorem integer_root_dvd_coefficient (P R : ℤ[X]) (k : ℕ) (c z : ℤ)
    (hz : z ≠ 0) (hcert : P = X ^ k * (C c + X * R)) (hroot : P.eval z = 0) :
    z ∣ c := by
  rw [hcert] at hroot
  simp only [eval_mul, eval_pow, eval_X, eval_add, eval_C] at hroot
  have h : c + z * R.eval z = 0 := (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hz)
  refine ⟨-R.eval z, ?_⟩
  calc
    c = -(z * R.eval z) := eq_neg_of_add_eq_zero_left h
    _ = z * -R.eval z := by ring

end Atlas.OrderArithmetic

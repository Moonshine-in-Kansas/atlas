import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-! Polynomial conjugation of an actual quadratic unipotent.  The hypotheses
are coefficient identities, before any use of finite-field evaluations.
-/
namespace Atlas.LinearAlgebra
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Expand in the central scalar parameter, retaining the cubic coefficient
needed for the short roots of G₂. -/
theorem quadratic_conjugation_expand (E E₂ X : A) (t : R) :
    (1 + t • E + t^2 • E₂) * X * (1 + (-t) • E + (-t)^2 • E₂) =
      X + t • (E*X-X*E) + t^2 • (E₂*X+X*E₂-E*X*E) +
        t^3 • (E*X*E₂-E₂*X*E) + t^4 • (E₂*X*E₂) := by
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
    smul_mul_assoc, smul_smul, neg_sq, neg_smul, smul_sub, smul_add,
    mul_neg, neg_mul, mul_assoc]
  module

/-- A coefficientwise check gives the full parameter identity over any
commutative ring; no division by 2 or 3 is used here. -/
theorem quadratic_conjugation_of_coefficients (E E₂ X C₁ C₂ C₃ : A)
    (h₁ : E*X-X*E=C₁)
    (h₂ : E₂*X+X*E₂-E*X*E=C₂)
    (h₃ : E*X*E₂-E₂*X*E=C₃)
    (h₄ : E₂*X*E₂=0) (t : R) :
    (1 + t • E + t^2 • E₂) * X * (1 + (-t) • E + (-t)^2 • E₂) =
      X + t • C₁ + t^2 • C₂ + t^3 • C₃ := by
  rw [quadratic_conjugation_expand, h₁, h₂, h₃, h₄, smul_zero, add_zero]

end Atlas.LinearAlgebra

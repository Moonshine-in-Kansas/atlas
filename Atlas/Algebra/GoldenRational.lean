import Mathlib.Algebra.QuadraticAlgebra.Discr
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open scoped QuadraticAlgebra

/-- The rational golden field, with distinguished root τ²=1+τ. -/
abbrev GoldenRational := QuadraticAlgebra ℚ 1 1

instance goldenRational_discriminant :
    Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℚ) 1)) :=
  ⟨by norm_num [QuadraticAlgebra.discr]⟩

def goldenTau : GoldenRational := QuadraticAlgebra.omega

def goldenSigma : GoldenRational := 1 - goldenTau

/-- The coefficient functional fixed in the icosian trace-lattice convention. -/
def goldenFunctional (z : GoldenRational) : ℚ := z.re

/-- Field trace, distinct from the chosen weighted functional. -/
def goldenTrace (z : GoldenRational) : ℚ := 2*z.re + z.im

def goldenAlpha : GoldenRational := ⟨3/5, -1/5⟩

theorem goldenTau_sq : goldenTau^2 = 1+goldenTau := by
  ext <;> norm_num [goldenTau, QuadraticAlgebra.omega, pow_two]

theorem goldenSigma_eq_star : goldenSigma = star goldenTau := by
  ext <;> simp [goldenSigma, goldenTau, QuadraticAlgebra.omega]

theorem goldenTau_mul_sigma : goldenTau*goldenSigma = -1 := by
  ext <;> norm_num [goldenSigma, goldenTau, QuadraticAlgebra.omega]

theorem goldenFunctional_add (x y : GoldenRational) :
    goldenFunctional (x+y)=goldenFunctional x+goldenFunctional y := rfl

theorem goldenFunctional_mul (x y : GoldenRational) :
    goldenFunctional (x*y)=x.re*y.re+x.im*y.im := by
  simp [goldenFunctional]

theorem goldenFunctional_sq (x : GoldenRational) :
    goldenFunctional (x^2)=x.re^2+x.im^2 := by
  simp [pow_two,goldenFunctional_mul]

theorem goldenFunctional_sq_nonneg (x : GoldenRational) :
    0 ≤ goldenFunctional (x^2) := by
  rw [goldenFunctional_sq]
  positivity

theorem goldenFunctional_sq_eq_zero (x : GoldenRational) :
    goldenFunctional (x^2)=0 ↔ x=0 := by
  rw [goldenFunctional_sq]
  constructor
  · intro h
    have hr : x.re=0 := by nlinarith [sq_nonneg x.re,sq_nonneg x.im]
    have hi : x.im=0 := by nlinarith [sq_nonneg x.re,sq_nonneg x.im]
    ext <;> simp [hr,hi]
  · rintro rfl; simp

theorem goldenFunctional_weighted_trace (x : GoldenRational) :
    goldenFunctional x=goldenTrace (goldenAlpha*x) := by
  simp [goldenFunctional,goldenTrace,goldenAlpha]
  ring

theorem goldenFunctional_pairing_nondegenerate (x : GoldenRational)
    (h : ∀ y, goldenFunctional (x*y)=0) : x=0 := by
  apply (goldenFunctional_sq_eq_zero x).mp
  simpa [pow_two] using h x

end Atlas.Algebra

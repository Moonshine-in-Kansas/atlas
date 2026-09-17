import Atlas.Fischer.CoordinateSpace
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Atlas.Fischer
open Atlas.Algebra

/-- Coordinates on the exact rational scalar field in the basis 1, theta. -/
def scalarRealThetaEquiv : Scalar ≃ₗ[ℚ] ℚ × ℚ where
  toFun z := (z.re - z.im / 2, z.im / 2)
  invFun p := ⟨p.1 + p.2, 2 * p.2⟩
  left_inv z := by ext <;> simp <;> ring
  right_inv p := by ext <;> simp <;> ring
  map_add' z w := by ext <;> simp <;> ring
  map_smul' a z := by ext <;> simp <;> ring

theorem scalarRealThetaEquiv_decomposition (z : Scalar) :
    z = (scalarRealThetaEquiv z).1 • (1 : Scalar) +
      (scalarRealThetaEquiv z).2 • theta := by
  have ht : theta = (⟨1,2⟩ : Scalar) := by
    ext <;> norm_num [theta,omega,rationalOmega,QuadraticAlgebra.omega]
  change z = (z.re - z.im / 2) • (1 : Scalar) + (z.im / 2) • theta
  rw [ht]
  apply QuadraticAlgebra.ext
  · change z.re = (z.re - z.im / 2) * 1 + (z.im / 2) * 1
    ring
  · change z.im = (z.re - z.im / 2) * 0 + (z.im / 2) * 2
    ring

theorem scalarRealThetaEquiv_star (z : Scalar) :
    scalarRealThetaEquiv (star z) =
      ((scalarRealThetaEquiv z).1, -(scalarRealThetaEquiv z).2) := by
  ext <;> simp [scalarRealThetaEquiv] <;> ring

theorem scalar_rational_dimension : Module.finrank ℚ Scalar = 2 :=
  QuadraticAlgebra.finrank_eq_two (-1 : ℚ) (-1)

/-- This is a rational restriction of scalars, not an asserted real vector space. -/
theorem coordinates_rational_dimension : Module.finrank ℚ Coordinates = 1566 := by
  have h := Module.finrank_mul_finrank ℚ Scalar Coordinates
  rw [scalar_rational_dimension,coordinates_dimension] at h
  omega

end Atlas.Fischer

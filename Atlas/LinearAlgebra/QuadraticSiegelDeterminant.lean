import Atlas.LinearAlgebra.QuadraticSiegel
import Mathlib.LinearAlgebra.Transvection.Basic

/-! # Unit determinant of actual quadratic Siegel isometries in every characteristic -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u v : V)

theorem siegel_transvection_factorization (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    siegelLinear Q u v =
      LinearMap.transvection (Q.polarBilin.flip v) u *
      LinearMap.transvection (-(Q.polarBilin.flip u)) v *
      LinearMap.transvection ((Q v) • Q.polarBilin.flip u) u := by
  apply LinearMap.ext
  intro x
  have huu : Q.polarBilin u u = 0 := by rw [polar_self, hu, mul_zero]
  have hvu : Q.polarBilin v u = 0 := (polar_swap Q v u).trans huv
  have hvv : Q.polarBilin v v = 2 * Q v := polar_self Q v
  change siegel Q u v x =
    LinearMap.transvection (Q.polarBilin.flip v) u
      (LinearMap.transvection (-(Q.polarBilin.flip u)) v
        (LinearMap.transvection ((Q v) • Q.polarBilin.flip u) u x))
  simp only [LinearMap.transvection.apply, LinearMap.flip_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, smul_eq_mul, map_add, map_smul, huu, huv, hvu, hvv,
    mul_zero, add_zero, siegel]
  module

variable [FiniteDimensional F V]

theorem siegelLinear_det (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    (siegelLinear Q u v).det = 1 := by
  have huu : Q.polarBilin u u = 0 := by rw [polar_self, hu, mul_zero]
  have hvu : Q.polarBilin v u = 0 := (polar_swap Q v u).trans huv
  rw [siegel_transvection_factorization Q u v hu huv]
  simp only [map_mul, LinearMap.transvection.det, LinearMap.flip_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul, huu, huv, hvu,
    neg_zero, mul_zero, add_zero, one_mul]

theorem siegelIsometry_det (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    (siegelIsometry Q u v hu huv).toLinearEquiv.det = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change (siegelLinear Q u v).det = (1 : F)
  change (siegelLinear Q u v).det = 1
  exact siegelLinear_det Q u v hu huv

end Atlas.Quadratic

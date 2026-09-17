import Atlas.LinearAlgebra.QuadraticReflection
import Atlas.LinearAlgebra.QuadraticSiegel
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Transvection.Basic

/-! # Determinants of full quadratic isometries and reflections -/
noncomputable section
namespace Atlas.Quadratic
open Matrix
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

theorem isometry_det_sq (hQ : Q.polarBilin.Nondegenerate) (g : Q.IsometryEquiv Q) :
    (g.toLinearEquiv.det : F)^2 = 1 := by
  classical
  let b := Module.finBasis F V
  have hb : LinearMap.BilinForm.comp Q.polarBilin g.toLinearEquiv.toLinearMap g.toLinearEquiv.toLinearMap = Q.polarBilin := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact isometry_polar Q g x y
  have hm := congrArg (LinearMap.BilinForm.toMatrix b) hb
  rw [LinearMap.BilinForm.toMatrix_comp b b] at hm
  have hd := congrArg Matrix.det hm
  simp only [Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hd
  have hne : (LinearMap.BilinForm.toMatrix b Q.polarBilin).det ≠ 0 :=
    (LinearMap.nondegenerate_iff_det_ne_zero b).mp hQ
  rw [LinearEquiv.coe_det]
  apply (mul_left_inj' hne).mp
  calc
    (LinearMap.det g.toLinearEquiv.toLinearMap)^2 *
        (LinearMap.BilinForm.toMatrix b Q.polarBilin).det =
        LinearMap.det g.toLinearEquiv.toLinearMap *
          (LinearMap.BilinForm.toMatrix b Q.polarBilin).det *
          LinearMap.det g.toLinearEquiv.toLinearMap := by ring
    _ = (LinearMap.BilinForm.toMatrix b Q.polarBilin).det := hd
    _ = 1 * (LinearMap.BilinForm.toMatrix b Q.polarBilin).det := (one_mul _).symm

theorem reflection_det (a : V) (ha : Q a ≠ 0) : (reflectionLinear Q a ha).det = -1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have he : (reflectionLinear Q a ha).toLinearMap =
      LinearMap.transvection (-(reflectionFunctional Q a)) a := by
    apply LinearMap.ext
    intro x
    simp only [LinearEquiv.coe_coe, reflectionLinear_apply, LinearMap.transvection.apply,
      LinearMap.neg_apply, reflectionFunctional, LinearMap.smul_apply, LinearMap.flip_apply,
      smul_eq_mul, sub_eq_add_neg, neg_smul]
  rw [he, LinearMap.transvection.det, LinearMap.neg_apply, reflectionFunctional_self Q a ha]
  change (1 : F) + -2 = -1
  ring

end Atlas.Quadratic

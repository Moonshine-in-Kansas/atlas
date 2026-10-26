import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

/-! A nonzero lower-root factorization in the actual two-dimensional matrices. -/
namespace Matrix.SL2
open Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]

theorem lower_bruhat (a : Fˣ) :
    SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (a : F) =
      SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (↑a⁻¹ : F) *
      diag2 (↑(-a⁻¹) : F) (-a⁻¹).ne_zero *
      (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F) *
        SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (-1 : F) *
        SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F)) *
      SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (↑a⁻¹ : F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, diag2_coe, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.transvection, Matrix.one_apply] <;> norm_num <;> field_simp <;> ring

end Matrix.SL2

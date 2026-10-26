import Atlas.LinearGroups.SL2Bruhat

/-! Gaussian factorization of a Weyl element followed by a nonzero upper root. -/
namespace Matrix.SL2
open Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]

theorem weyl_upper_gaussian (a : Fˣ) :
    (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F) *
      SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (-1 : F) *
      SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F)) *
      SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (a : F) =
    SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (↑(-a⁻¹) : F) *
      diag2 (↑(-a⁻¹) : F) (-a⁻¹).ne_zero *
      SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (↑a⁻¹ : F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, diag2_coe, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.transvection, Matrix.one_apply] <;> norm_num <;> field_simp <;> ring

end Matrix.SL2

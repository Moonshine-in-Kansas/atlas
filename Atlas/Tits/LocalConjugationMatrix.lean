import Atlas.Tits.BinaryTranslationConjugation

namespace Atlas.Tits
open Atlas.Rudvalis

 theorem localCodeN_inverse_row_matrix :
    binaryLinearMatrix (codeBlockLinearHom (coupleCodeD ^ 4)).symm = localRowMatrix ^ 2 := by
  let A := codeBlockLinearHom (coupleCodeD ^ 4)
  apply binaryMatrix_eq_of_apply
  intro x
  rw [binaryLinearMatrix_apply]
  apply A.injective
  rw [LinearEquiv.apply_symm_apply]
  rw [← binaryLinearMatrix_apply A, localCodeN_row_matrix, ← matrixAt_mul,
    ← pow_succ', localRowMatrix_cube]
  exact (Matrix.one_mulVec x).symm

 theorem localCodeN_matrix_difference (M : BinaryMatrix) :
    binaryMatrixConjugate (codeBlockLinearHom (coupleCodeD ^ 4)) M - M =
      localMatrixDifference M := by
  rw [binaryMatrixConjugate, localCodeN_row_matrix, localCodeN_inverse_row_matrix]
  rfl

end Atlas.Tits

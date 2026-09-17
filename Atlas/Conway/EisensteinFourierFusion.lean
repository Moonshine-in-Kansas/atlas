import Atlas.Conway.EisensteinFourier
import Atlas.Conway.EisensteinFourierFusionData
import Atlas.Conway.EisensteinCoordinateIsometries

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators Matrix

private theorem fusion_diagonal_apply (t : TernaryWord) (z : EisensteinRationalCoordinates) :
    eisensteinFusionDiagonalMatrix t *ᵥ z = eisensteinRationalDiagonal t z := by
  funext i
  simp [eisensteinFusionDiagonalMatrix,Matrix.mulVec,dotProduct,
    Matrix.diagonal,eisensteinRationalDiagonal]

private theorem fusion_monomial_apply (z : EisensteinRationalCoordinates) :
    eisensteinFusionMonomialMatrix *ᵥ z =
      eisensteinRationalDiagonal eisensteinFusionOutputWord
        (eisensteinRationalPermutation eisensteinFusionPermutation z) := by
  funext i
  simp [eisensteinFusionMonomialMatrix,Matrix.mulVec,dotProduct,ite_mul,
    eisensteinRationalDiagonal,eisensteinRationalPermutation]

/-- A specific nonconstant code phase fuses to a local monomial with nontrivial permutation. -/
theorem eisensteinFourier_fusion (z : EisensteinRationalCoordinates) :
    eisensteinFourier (eisensteinRationalDiagonal eisensteinFusionInputWord
      (eisensteinFourier.symm z)) =
    eisensteinRationalDiagonal eisensteinFusionOutputWord
      (eisensteinRationalPermutation eisensteinFusionPermutation z) := by
  rw [eisensteinFourier_apply,eisensteinFourier_symm_apply,← fusion_diagonal_apply,
    Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,eisensteinFourier_fusion_matrix]
  exact fusion_monomial_apply z

def eisensteinFourierFusedIsometry : eisensteinHermitianGroup :=
  eisensteinFourierIsometry *
    eisensteinPhaseIsometries (Multiplicative.ofAdd eisensteinFusionInput) *
      eisensteinFourierIsometry⁻¹

theorem eisensteinFourierFusedIsometry_apply (z : EisensteinRationalCoordinates) :
    eisensteinFourierFusedIsometry.val z =
      eisensteinRationalDiagonal eisensteinFusionOutputWord
        (eisensteinRationalPermutation eisensteinFusionPermutation z) :=
  eisensteinFourier_fusion z

/-- The fused element lies in the actual coordinate monomial subgroup. -/
theorem eisensteinFourier_fusion_group :
    eisensteinFourierFusedIsometry =
      eisensteinPhaseIsometries (Multiplicative.ofAdd eisensteinFusionOutput) *
        eisensteinCoordinateIsometries
          ⟨eisensteinFusionPermutation,eisensteinFusionPermutation_mem⟩ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  exact eisensteinFourierFusedIsometry_apply z

theorem eisensteinFusionInput_phase_ne_zero :
    (Submodule.Quotient.mk eisensteinFusionInput : TernaryPhaseModule) ≠ 0 := by
  intro h
  exact eisensteinFusionInput_not_constant ((Submodule.Quotient.mk_eq_zero _).mp h)

end Atlas.Conway

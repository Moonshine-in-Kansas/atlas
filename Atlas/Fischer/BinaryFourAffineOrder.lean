import Atlas.Fischer.MathieuOctadAffineAction
import Atlas.LinearAlgebra.AffineEquivParameters
import Atlas.LinearGroups.ProjectiveGeneralLinear

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

noncomputable def binaryFourLinearMatrixEquiv :
    Matrix.GeneralLinearGroup (Fin 4) Bit ≃* (BinaryFourSpace ≃ₗ[Bit] BinaryFourSpace) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem binaryFourLinear_order : Nat.card (BinaryFourSpace ≃ₗ[Bit] BinaryFourSpace) = 20160 := by
  rw [← Nat.card_congr binaryFourLinearMatrixEquiv.toEquiv, Atlas.card_gl]
  norm_num [Bit, Nat.card_eq_fintype_card, Fin.prod_univ_succ]

theorem binaryFourAffine_order : Nat.card (BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace) = 322560 := by
  rw [Atlas.LinearAlgebra.affineEquiv_card, binaryFourLinear_order]
  norm_num [BinaryFourSpace,Nat.card_eq_fintype_card,Bit]

/-- Surjectivity onto the full affine group follows from the proved faithful
geometric action and its exact order, not from recognition of a sporadic group. -/
theorem mathieuOctadAffineHom_surjective (O : Octad) :
    Function.Surjective (mathieuOctadAffineHom O) := by
  letI : Finite (BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace) :=
    Nat.finite_of_card_ne_zero (by rw [binaryFourAffine_order]; decide)
  exact ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨mathieuOctadAffineHom_injective O,
      (mathieuOctadStabilizer_order O).trans binaryFourAffine_order.symm⟩).surjective

noncomputable def mathieuOctadAffineEquivalence (O : Octad) :
    MathieuOctadStabilizer O ≃* (BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace) :=
  MulEquiv.ofBijective (mathieuOctadAffineHom O)
    ⟨mathieuOctadAffineHom_injective O, mathieuOctadAffineHom_surjective O⟩

end Atlas.Fischer

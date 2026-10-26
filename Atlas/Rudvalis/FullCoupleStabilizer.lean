import Atlas.Rudvalis.QuartetLocalTransitivity

namespace Atlas.Rudvalis

/-- The explicitly generated couple group is the full pointwise Gaussian couple stabilizer. -/
theorem coupleFusionGroup_eq_pair_stabilizer :
    coupleFusionGroup=MulAction.stabilizer gaussianLatticeGroup localReferenceCross ⊓
      MulAction.stabilizer gaussianLatticeGroup referenceSecondCross := by
  apply le_antisymm coupleFusionGroup_le_pair_stabilizer
  intro g hg
  change (g • localReferenceCross=localReferenceCross) ∧
    (g • referenceSecondCross=referenceSecondCross) at hg
  let Q := gaussianImage g (coordinateRowFrame (rowLabel 0))
  have hQ : IsQuartet Q := (isQuartet_gaussianImage g _).mpr (coordinateRowFrame_isQuartet _)
  have hc : referenceCouple⊆Q := by
    have hrow := (referenceCouple_subset_row_iff (rowLabel 0)).mpr rfl
    rintro z (rfl|rfl)
    · exact ⟨localReferenceCross,hrow (Or.inl rfl),hg.1⟩
    · exact ⟨referenceSecondCross,hrow (Or.inr rfl),hg.2⟩
  obtain ⟨a,ha⟩ := coupleFusion_reference_quartet_transport Q hQ hc
  have hrow : gaussianImage (a.val⁻¹*g) (coordinateRowFrame (rowLabel 0))=
      coordinateRowFrame (rowLabel 0) := by
    rw [gaussianImage_mul]
    change gaussianImage a.val⁻¹ Q=_
    rw [←ha,gaussianImage_inv]
  obtain ⟨h,hh⟩ := gaussian_coordinateRow_stabilizer_le_code (a.val⁻¹*g) (rowLabel 0) hrow
  have hfix := coupleFusionGroup_fix a
  have hhfix : h∈codeCoupleStabilizer := by
    constructor
    · change h • localReferenceCross=localReferenceCross
      rw [←codeGaussianHom_cross,hh,mul_smul,hg.1,←hfix.1,inv_smul_smul]
      exact hfix.1.symm
    · change h • referenceSecondCross=referenceSecondCross
      rw [←codeGaussianHom_cross,hh,mul_smul,hg.2,←hfix.2,inv_smul_smul]
      exact hfix.2.symm
  have hm := coupleGaussianHom_mem ⟨h,hhfix⟩
  change codeGaussianHom h∈coupleFusionGroup at hm
  rw [hh] at hm
  have hm' := coupleFusionGroup.mul_mem a.prop hm
  simpa only [mul_inv_cancel_left] using hm'

end Atlas.Rudvalis

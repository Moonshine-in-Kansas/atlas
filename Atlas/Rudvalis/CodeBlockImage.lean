import Atlas.Rudvalis.CodeProjectionCoordinates
import Atlas.Rudvalis.BlockLinearGenerators

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def codeBlockLinearHom : codeGroup →* (E ≃ₗ[Bit] E) :=
  binaryBlockLinearHom.comp codePermutationHom

theorem codeBlockLinear_coordinates (g : codeGroup) (z : Coordinate) :
    codeBlockLinearHom g z.1.val=(g.val.right z).1.val := by
  change binaryBlockLinearEquiv (codePermutationHom g) z.1.val=_
  rw [binaryBlockLinearEquiv_point]
  exact congrArg Subtype.val (binaryBlockPermutation_coordinates (codePermutationHom g) z).symm

theorem original_congr_apply (p : Equiv.Perm SeedCoordinate) (z : SeedCoordinate) :
    originalCoordinateEquiv.permCongrHom p (originalCoordinateEquiv z)=originalCoordinateEquiv (p z) := by
  simp [Equiv.permCongrHom,Equiv.permCongr,Equiv.equivCongr]

theorem codeP_block_image : codeBlockLinearHom codeP=binaryPLinear := by
  apply LinearEquiv.ext
  intro x
  by_cases hx : x=0
  · subst x; simp
  obtain ⟨r,hr⟩ := rowLabel_bijective.2 (⟨x,hx⟩ : Point)
  have h := codeBlockLinear_coordinates codeP (originalCoordinateEquiv (r,0))
  rw [codeP_right,original_congr_apply] at h
  have hc : ∀ r : Fin 7, (rowLabel (seedPMonomial.right (r,0)).1).val=
      binaryPMatrix.mulVec (rowLabel r).val := by decide +kernel
  change codeBlockLinearHom codeP (rowLabel r).val=(rowLabel (seedPMonomial.right (r,0)).1).val at h
  rw [hc r] at h
  simpa only [hr,binaryPLinear_apply] using h

theorem codeR_block_image : codeBlockLinearHom codeR=binaryRLinear := by
  apply LinearEquiv.ext
  intro x
  by_cases hx : x=0
  · subst x; simp
  obtain ⟨r,hr⟩ := rowLabel_bijective.2 (⟨x,hx⟩ : Point)
  have h := codeBlockLinear_coordinates codeR (originalCoordinateEquiv (r,0))
  rw [codeR_right,original_congr_apply] at h
  have hc : ∀ r : Fin 7, (rowLabel (seedRMonomial.right (r,0)).1).val=
      binaryRMatrix.mulVec (rowLabel r).val := by decide +kernel
  change codeBlockLinearHom codeR (rowLabel r).val=(rowLabel (seedRMonomial.right (r,0)).1).val at h
  rw [hc r] at h
  simpa only [hr,binaryRLinear_apply] using h

theorem codeBlockLinearHom_surjective : Function.Surjective codeBlockLinearHom := by
  apply MonoidHom.range_eq_top.mp
  apply binaryPR_generate
  · exact ⟨codeP,codeP_block_image⟩
  · exact ⟨codeR,codeR_block_image⟩

end Atlas.Rudvalis

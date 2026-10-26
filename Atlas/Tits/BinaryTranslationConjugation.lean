import Atlas.Tits.LocalRowMatrix

namespace Atlas.Tits
open Atlas.Rudvalis
open scoped commutatorElement

/-- Translation conjugation depends only on the inherited row-linear action. -/
theorem binary_translation_conjugate (g : binaryPermutationGroup) (M : BinaryMatrix) :
    g * coordinateTranslationHom (Multiplicative.ofAdd M) * g⁻¹ =
      coordinateTranslationHom (Multiplicative.ofAdd
        (binaryMatrixConjugate (binaryBlockLinearHom g) M)) := by
  let A := binaryBlockLinearHom g
  choose t ht using section_difference_origin A
  let s := binarySectionGroupLift A t ht
  have hs : binaryBlockLinearHom s = A := binarySectionGroupLift_blocks A t ht
  have hk : g*s⁻¹ ∈ binaryBlockLinearHom.ker := by
    change binaryBlockLinearHom (g*s⁻¹) = 1
    rw [map_mul, map_inv, hs]
    exact mul_inv_cancel _
  rw [binaryBlockLinearHom_kernel_translations] at hk
  obtain ⟨B, hB⟩ := hk
  have hg : g = coordinateTranslationHom B * s := by
    rw [hB]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  calc
    g * coordinateTranslationHom (Multiplicative.ofAdd M) * g⁻¹ =
        coordinateTranslationHom B *
          (s * coordinateTranslationHom (Multiplicative.ofAdd M) * s⁻¹) *
          (coordinateTranslationHom B)⁻¹ := by rw [hg]; group
    _ = coordinateTranslationHom B *
          coordinateTranslationHom (Multiplicative.ofAdd (binaryMatrixConjugate A M)) *
          (coordinateTranslationHom B)⁻¹ := by
      rw [binarySection_translation_conjugate A t ht M]
    _ = coordinateTranslationHom (Multiplicative.ofAdd (binaryMatrixConjugate A M)) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      simp [mul_comm, mul_left_comm, mul_assoc]

theorem binary_translation_commutator (g : binaryPermutationGroup) (M : BinaryMatrix) :
    ⁅g, coordinateTranslationHom (Multiplicative.ofAdd M)⁆ =
      coordinateTranslationHom (Multiplicative.ofAdd
        (binaryMatrixConjugate (binaryBlockLinearHom g) M - M)) := by
  rw [commutatorElement_def, binary_translation_conjugate, ← map_inv, ← map_mul,
    sub_eq_add_neg]
  rfl

end Atlas.Tits

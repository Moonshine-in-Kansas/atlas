import Atlas.Conway.IcosianReflectionUnipotentImage

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes

theorem icosianReflectionSwap_reduction (p : Fin 2) :
    icosianMonomialReduction (icosianReflectionSwapMonomial p)=
      SemidirectProduct.inr (Equiv.swap 0 (icosianReflectionEdgePartner p)) := by
  apply SemidirectProduct.ext
  · funext i
    exact map_one icosianNormOneReduction
  · rfl

theorem icosianReflection_swap_image (p : Fin 2) :
    (SemidirectProduct.inr (Equiv.swap 0 (icosianReflectionEdgePartner p)) :
      IcosianGlueMonomialGroup GoldenFour)∈icosianReflectionGlueImage := by
  rw [← icosianReflectionSwap_reduction]
  exact icosianReflectionGlueImage_mem_of_actual_word _ _
    (icosianReflectionEdgeGenerator_mem 0 p) (icosianReflectionSwap_linear p)

/-- Six words in the two coordinate transpositions, a bounded three-point fact. -/
theorem icosian_three_permutation_cases : ∀ p : Equiv.Perm (Fin 3),
    p=1 ∨ p=Equiv.swap 0 1 ∨ p=Equiv.swap 0 2 ∨
    p=Equiv.swap 0 1*Equiv.swap 0 2 ∨ p=Equiv.swap 0 2*Equiv.swap 0 1 ∨
    p=Equiv.swap 0 1*Equiv.swap 0 2*Equiv.swap 0 1 := by decide +kernel

theorem icosianReflection_permutation_image (p : Equiv.Perm (Fin 3)) :
    (SemidirectProduct.inr p : IcosianGlueMonomialGroup GoldenFour)∈icosianReflectionGlueImage := by
  have h01 := icosianReflection_swap_image 0
  have h02 := icosianReflection_swap_image 1
  change (SemidirectProduct.inr (Equiv.swap 0 1) : IcosianGlueMonomialGroup GoldenFour)∈
    icosianReflectionGlueImage at h01
  change (SemidirectProduct.inr (Equiv.swap 0 2) : IcosianGlueMonomialGroup GoldenFour)∈
    icosianReflectionGlueImage at h02
  rcases icosian_three_permutation_cases p with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [map_one] using icosianReflectionGlueImage.one_mem
  · exact h01
  · exact h02
  · simpa only [map_mul] using icosianReflectionGlueImage.mul_mem h01 h02
  · simpa only [map_mul] using icosianReflectionGlueImage.mul_mem h02 h01
  · simpa only [map_mul] using icosianReflectionGlueImage.mul_mem
      (icosianReflectionGlueImage.mul_mem h01 h02) h01

end Atlas.Conway

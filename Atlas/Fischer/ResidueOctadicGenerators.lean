import Atlas.Fischer.ResidueGeneratedFrames
import Atlas.Fischer.OctadicGeneratedFrameTranslation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadicDistinguished_mem_residueGenerated (S : Finset Omega)
    (O : Octad) (hSO : S ⊆ O.val) (χ : OctadicCharacter O) :
    distinguishedRootElement (.inr (.inl ⟨O,χ⟩)) ∈ residueGenerated S := by
  apply Subgroup.subset_closure
  right
  refine ⟨⟨_,⟨.inr (.inl ⟨O,χ⟩),rfl⟩,?_,?_⟩,rfl⟩
  · rintro ⟨i,hi,he⟩
    have h := distinguishedRootElement_injective he
    cases h
  · intro i hi
    have hh : hermitian (reflectingRootParameterVector (.inl i))
        (reflectingRootParameterVector (.inr (.inl ⟨O,χ⟩))) ^ 3=1 := by
      change hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration O) χ)^3=1
      rw [hermitian_basicAxis_octadic,if_pos (hSO hi),one_pow]
    apply Subtype.ext
    exact displayedRootRay_unit_commute (.inl i) (.inr (.inl ⟨O,χ⟩)) hh

/-- Equal-parity pairs will supply the full local affine translation kernels;
membership already follows from the two actual residue generators. -/
theorem octadicGeneratedPhasePair_mem_residueGenerated (S : Finset Omega)
    (O : Octad) (hSO : S ⊆ O.val) (χ ψ : OctadicCharacter O) :
    fullSemilinearRayProjection (octadicGeneratedPhasePair O χ ψ) ∈ residueGenerated S := by
  change fullSemilinearRayProjection
    (displayedRootAutomorphism (.inr (.inl ⟨O,ψ⟩)) *
      displayedRootAutomorphism (.inr (.inl ⟨O,χ⟩))) ∈ _
  rw [map_mul]
  exact (residueGenerated S).mul_mem
    (octadicDistinguished_mem_residueGenerated S O hSO ψ)
    (octadicDistinguished_mem_residueGenerated S O hSO χ)

end Atlas.Fischer

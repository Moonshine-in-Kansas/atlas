import Atlas.Lattices.EisensteinComparisonChecks
import Atlas.Lattices.EisensteinIntegralGenerators

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

private theorem source_generator_surjective {g : EisensteinCoordinates}
    (hg : g ∈ eisensteinGeneratorSet) :
    ∃ j, eisensteinComparisonSourceGenerator j = g := by
  rcases hg with ((rfl | ⟨j, rfl⟩) | ⟨i, rfl⟩) | rfl
  · exact ⟨0, rfl⟩
  · refine ⟨⟨j.val+1, by omega⟩, ?_⟩
    simp [eisensteinComparisonSourceGenerator, show j.val+1≠0 by omega,
      show j.val+1<7 by omega]
  · refine ⟨⟨i.val+7, by omega⟩, ?_⟩
    simp [eisensteinComparisonSourceGenerator, show i.val+7≠0 by omega,
      show ¬i.val+7<7 by omega, show i.val+7<19 by omega]
  · exact ⟨19, rfl⟩

/-- Forward containment, proved for all congruence vectors through the integral generators. -/
theorem eisensteinComparison_forward (z : EisensteinRationalCoordinates)
    (hz : z ∈ rationalEisensteinLattice) : eisensteinComparison z ∈ rationalLeech := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz
  let S : Submodule ℤ EisensteinCoordinates := rationalLeech.comap
    ((eisensteinComparison.toLinearMap.restrictScalars ℤ).comp eisensteinCoordinateEmbedding)
  have h (u : Fin 2) (g : EisensteinCoordinates) (hg : g ∈ eisensteinGeneratorSet) :
      eisensteinComparisonPhase u • g ∈ S := by
    obtain ⟨j, rfl⟩ := source_generator_surjective hg
    obtain ⟨x, hx, he⟩ := eisensteinComparison_generator_check j u
    change eisensteinComparison (eisensteinCoordinateEmbedding _) ∈ rationalLeech
    rw [he]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hs : eisensteinLeechModule.restrictScalars ℤ ≤ S :=
    eisensteinLeechModule_integral_generators S
      (fun g hg => by simpa [eisensteinComparisonPhase] using h 0 g hg)
      (fun g hg => by simpa [eisensteinComparisonPhase] using h 1 g hg)
  exact hs hv

private theorem oldPoint_crossIndex (i : Omega) :
    eisensteinOldPoint (eisensteinCrossIndex i) = i := by
  revert i; decide +kernel

/-- Reverse containment, using the retained binary Golay generating criterion. -/
theorem eisensteinComparison_reverse (x : RationalCoordinates)
    (hx : x ∈ rationalLeech) : eisensteinComparison.symm x ∈ rationalEisensteinLattice := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
  let P : Submodule ℤ IntegerCoordinates := rationalEisensteinLattice.comap
    ((eisensteinComparison.symm.toLinearMap.restrictScalars ℤ).comp rationalEmbedding)
  have h (j : Fin 38) : eisensteinComparisonTargetGenerator j ∈ P := by
    change eisensteinComparison.symm (rationalEmbedding _) ∈ rationalEisensteinLattice
    rw [← eisensteinComparison_preimage_check, eisensteinComparison.symm_apply_apply]
    exact Submodule.mem_map.mpr ⟨_, eisensteinLeechPreimage_mem j, rfl⟩
  have hp : leech ≤ P := leech_le_of_generators P ((0,0),0)
    (fun i => by
      have hi := h ⟨(eisensteinCrossIndex i).val, by omega⟩
      simpa [eisensteinComparisonTargetGenerator, (eisensteinCrossIndex i).isLt,
        oldPoint_crossIndex] using hi)
    (by simpa [eisensteinComparisonTargetGenerator] using h 24)
    (fun j => by
      have hj := h ⟨j.val+25, by omega⟩
      simpa [eisensteinComparisonTargetGenerator, show ¬j.val+25<24 by omega,
        show j.val+25≠24 by omega, show j.val+25<37 by omega] using hj)
    (by simpa [eisensteinComparisonTargetGenerator] using h 37)
  exact hp hv

/-- Equality with the SAME retained Golay Leech lattice, in both directions. -/
theorem eisensteinComparison_lattice_iff (z : EisensteinRationalCoordinates) :
    z ∈ rationalEisensteinLattice ↔ eisensteinComparison z ∈ rationalLeech := by
  constructor
  · exact eisensteinComparison_forward z
  · intro h
    simpa only [LinearEquiv.symm_apply_apply] using eisensteinComparison_reverse (eisensteinComparison z) h

end Atlas.Lattices

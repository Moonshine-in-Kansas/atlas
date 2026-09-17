import Atlas.Conway.EisensteinGeneratedNineFrames
import Atlas.Conway.EisensteinGeneratedHexadFrames
import Atlas.Conway.EisensteinGeneratedBalancedNine

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices MulAction
attribute [local irreducible] eisensteinNineHexadFamily

theorem eisensteinSuborbitFrames_generated (i : Fin 13) :
    eisensteinSuborbitFrames i ⊆ eisensteinGeneratedFrames := by
  fin_cases i
  · intro F hF
    have h : F=eisensteinStandardFrame := hF
    subst F
    exact eisensteinGeneratedFrames_standard
  · exact eisensteinGeneratedFrames_triad
  · exact eisensteinGeneratedFrames_hexad
  · exact eisensteinGeneratedFrames_nineHexad 1 (by decide)
  · exact eisensteinGeneratedFrames_nineHexad 2 (by decide)
  · exact eisensteinGeneratedFrames_heavy
  · exact eisensteinGeneratedFrames_pair false
  · exact eisensteinGeneratedFrames_pair true
  · exact eisensteinGeneratedFrames_balanced
  · exact eisensteinGeneratedFrames_unitTriad 0
  · exact eisensteinGeneratedFrames_unitTriad 1
  · exact eisensteinGeneratedFrames_unitTriad 2
  · exact eisensteinGeneratedFrames_balancedNine

theorem eisensteinGeneratedFrames_all (F : EisensteinFrame) :
    F ∈ eisensteinGeneratedFrames := by
  obtain ⟨i,hi⟩ := eisensteinSuborbitFrames_cover F
  exact eisensteinSuborbitFrames_generated i hi

/-- The full local stabilizer and the actual corrected Fourier isometry
generate the full Hermitian isometry group of the Eisenstein Leech lattice. -/
theorem eisensteinGeneratedGroup_eq_top : eisensteinGeneratedGroup=⊤ := by
  apply Atlas.GroupTheory.subgroup_eq_top_of_full_stabilizer
    eisensteinGeneratedGroup eisensteinStandardFrame
  · rw [eisensteinStandardFrame_stabilizer]
    exact eisensteinLocal_le_generated
  · intro g
    exact eisensteinGeneratedFrames_all (g • eisensteinStandardFrame)

theorem eisensteinHermitian_frame_transitive :
    IsPretransitive eisensteinHermitianGroup EisensteinFrame := by
  apply (isPretransitive_iff_orbit_eq_univ (G := eisensteinHermitianGroup) eisensteinStandardFrame).mpr
  apply Set.eq_univ_iff_forall.mpr
  intro F
  exact orbit_subgroup_subset eisensteinGeneratedGroup eisensteinStandardFrame
    (eisensteinGeneratedFrames_all F)

end Atlas.Conway

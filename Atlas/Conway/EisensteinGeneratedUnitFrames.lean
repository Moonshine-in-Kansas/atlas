import Atlas.Conway.EisensteinGeneratedFrames
import Atlas.Conway.EisensteinUnitFourier
import Atlas.Conway.EisensteinUnitFrameCount

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction

theorem eisensteinGeneratedFrames_heavy :
    eisensteinHeavyUnitFrames ⊆ eisensteinGeneratedFrames := by
  rw [eisensteinHeavyUnitFrames_orbit]
  apply eisensteinGeneratedFrames_localOrbit
  apply (eisensteinGeneratedFrames_fourier_iff _).mp
  rw [eisensteinFourier_heavy_balanced]
  exact eisensteinGeneratedFrames_balanced (eisensteinBalancedParameterFrame_mem _)

theorem eisensteinGeneratedFrames_pair (b : Bool) :
    eisensteinPairUnitFrames b ⊆ eisensteinGeneratedFrames := by
  rw [eisensteinPairUnitFrames_orbit]
  apply eisensteinGeneratedFrames_localOrbit
  apply (eisensteinGeneratedFrames_fourier_iff _).mp
  rw [eisensteinFourier_pair_balanced]
  exact eisensteinGeneratedFrames_balanced (eisensteinBalancedParameterFrame_mem _)

theorem eisensteinGeneratedFrames_unitTriad (r : Fin 3) :
    eisensteinTriadUnitFrames r ⊆ eisensteinGeneratedFrames := by
  rw [eisensteinTriadUnitFrames_orbit]
  apply eisensteinGeneratedFrames_localOrbit
  apply (eisensteinGeneratedFrames_fourier_iff _).mp
  rw [eisensteinFourier_unitTriad_balanced]
  exact eisensteinGeneratedFrames_balanced (eisensteinBalancedParameterFrame_mem _)

/-- Every one of the155277 nonzero-residue frames is reached from the standard
frame by the actual full local subgroup and Fourier isometry. -/
theorem eisensteinGeneratedFrames_unit :
    eisensteinUnitResidueFrames ⊆ eisensteinGeneratedFrames := by
  intro F hF
  rcases (eisensteinUnitResidueFrames_mem F).mp hF with hh | ⟨b,hb⟩ | ⟨r,hr⟩
  · exact eisensteinGeneratedFrames_heavy hh
  · exact eisensteinGeneratedFrames_pair b hb
  · exact eisensteinGeneratedFrames_unitTriad r hr

end Atlas.Conway

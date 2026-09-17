import Atlas.Conway.EisensteinSuborbitFamilies
import Atlas.Conway.EisensteinGeneratedHexadFrames
import Atlas.Conway.EisensteinGeneratedUnitFrames

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices MulAction

theorem eisensteinStandardFrame_localOrbit :
    orbit eisensteinCoordinateFrameStabilizer eisensteinStandardFrame =
      {eisensteinStandardFrame} := by
  ext F
  constructor
  · rintro ⟨g,rfl⟩
    have hg : g.val ∈ stabilizer eisensteinHermitianGroup eisensteinStandardFrame :=
      (le_of_eq eisensteinStandardFrame_stabilizer.symm) g.property
    exact hg
  · rintro rfl
    exact mem_orbit_self _

/-- The eleven full local orbits already established independently of the two
constant norm-nine phase families. -/
theorem eisensteinElevenSuborbit_orbit (i : Fin 13) (h3 : i≠3) (h4 : i≠4) :
    ∃ F : EisensteinFrame,
      eisensteinSuborbitFrames i = orbit eisensteinCoordinateFrameStabilizer F := by
  fin_cases i
  · exact ⟨eisensteinStandardFrame,eisensteinStandardFrame_localOrbit.symm⟩
  · obtain ⟨F,hF⟩ := Finset.card_pos.mp
      (show 0<eisensteinTriadFamily.card by rw [eisensteinTriadFamily_card]; decide)
    exact ⟨F,(eisensteinTriadFamily_orbit F hF).symm⟩
  · obtain ⟨F,hF⟩ := Finset.card_pos.mp
      (show 0<eisensteinHexadFamily.card by rw [eisensteinHexadFamily_card]; decide)
    exact ⟨F,(eisensteinHexadFamily_orbit F hF).symm⟩
  · exact (h3 rfl).elim
  · exact (h4 rfl).elim
  · exact ⟨eisensteinHeavyUnitFrame 0 0,eisensteinHeavyUnitFrames_orbit⟩
  · exact ⟨eisensteinPairUnitFrame false eisensteinOrderedBasePair 0,eisensteinPairUnitFrames_orbit false⟩
  · exact ⟨eisensteinPairUnitFrame true eisensteinOrderedBasePair 0,eisensteinPairUnitFrames_orbit true⟩
  · obtain ⟨F,hF⟩ := Finset.card_pos.mp
      (show 0<eisensteinBalancedFamily.card by rw [eisensteinBalancedFamily_card]; decide)
    exact ⟨F,(eisensteinBalancedFamily_orbit F hF).symm⟩
  · exact ⟨eisensteinTriadUnitFrame 0 eisensteinBaseTriadEmbedding 0,eisensteinTriadUnitFrames_orbit 0⟩
  · exact ⟨eisensteinTriadUnitFrame 1 eisensteinBaseTriadEmbedding 0,eisensteinTriadUnitFrames_orbit 1⟩
  · exact ⟨eisensteinTriadUnitFrame 2 eisensteinBaseTriadEmbedding 0,eisensteinTriadUnitFrames_orbit 2⟩
  · obtain ⟨F,hF⟩ := Finset.card_pos.mp
      (show 0<eisensteinBalancedNineFamily.card by rw [eisensteinBalancedNineFamily_card]; decide)
    exact ⟨F,(eisensteinBalancedNineFamily_orbit F hF).symm⟩

theorem eisensteinElevenSuborbit_invariant (i : Fin 13) (h3 : i≠3) (h4 : i≠4)
    (g : eisensteinCoordinateFrameStabilizer) (F : EisensteinFrame)
    (hF : F ∈ eisensteinSuborbitFrames i) : g.val • F ∈ eisensteinSuborbitFrames i := by
  obtain ⟨X,hX⟩ := eisensteinElevenSuborbit_orbit i h3 h4
  rw [hX] at hF ⊢
  exact mapsTo_smul_orbit g X hF

end Atlas.Conway

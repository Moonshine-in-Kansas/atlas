import Atlas.Fischer.ParkerOctadAssociatorObstruction

namespace Atlas.Fischer
open Atlas.Codes

/-- The actual standard Parker automorphism extension by the actual Golay
cocode has no group-homomorphic section. -/
theorem parkerStandardProjection_nonsplit :
    ¬ ∃ s : Mathieu24CodeModel →* ParkerStandardGroup,
      parkerStandardProjection.comp s = MonoidHom.id _ := by
  rintro ⟨s,hs⟩
  obtain ⟨q,hq,heq⟩ := parkerSection_equivariant_octad_representatives s hs countingCanonicalD
  obtain ⟨e,he⟩ := parkerSection_uniform_octad_sign s q hq heq
  exact parkerOctad_uniform_sign_impossible q hq e he

end Atlas.Fischer

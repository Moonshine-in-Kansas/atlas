import Atlas.Fischer.ResidueOctadicGenerators
import Atlas.Fischer.OctadicFrameTranslationCoordinates
import Atlas.Fischer.MathieuTranslationGeneration

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def residueAlgebraFramePreimage (S : Finset Omega) : Subgroup basicFrameStabilizer :=
  ((residueGenerated S).comap fullSemilinearRayProjection).comap basicFrameStabilizer.subtype

def residueFrameMathieuImage (S : Finset Omega) : Subgroup Mathieu24CodeModel :=
  (residueAlgebraFramePreimage S).map basicFrameCoordinateHom

theorem octadTranslations_le_residueFrameMathieuImage (S : Finset Omega) :
    octadTranslationGenerators S ⊆ residueFrameMathieuImage S := by
  rintro g ⟨O,hSO,u,rfl⟩
  obtain ⟨t,ht⟩ := mathieuOctadPointwise_exists_character O u
  have hp : (0 : OctadicCharacter O) (octadShortenedOne O)=t.val (octadShortenedOne O) :=
    t.property.symm
  refine ⟨⟨octadicGeneratedPhasePair O 0 t.val,
    octadicGeneratedPhasePair_frame O 0 t.val hp⟩,
    octadicGeneratedPhasePair_mem_residueGenerated S O hSO 0 t.val,?_⟩
  rw [octadicGeneratedPhasePair_coordinate O t hp,ht]
  rfl

/-- The full actual marked Mathieu fixer is supplied by retained translation
generation, rather than an assumed local group shape. -/
theorem mathieuFixing_le_residueFrameMathieuImage (S : Finset Omega) (hS : S.card ≤ 2) :
    fixingSubgroup Mathieu24CodeModel (S : Set Omega) ≤ residueFrameMathieuImage S := by
  rw [← mathieuTranslationGenerated_eq_fixing S hS]
  exact (Subgroup.closure_le _).mpr (octadTranslations_le_residueFrameMathieuImage S)

end Atlas.Fischer

import Atlas.Fischer.OctadQuadraticRange
import Atlas.Fischer.OctadEvenRestriction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

def binaryAffineInQuadratic : Submodule Bit binaryQuadraticCode :=
  binaryAffineCode.comap binaryQuadraticCode.subtype

abbrev BinaryQuadraticClasses := binaryQuadraticCode ⧸ binaryAffineInQuadratic

def octadQuadraticRestriction (O : Octad) : golay →ₗ[Bit] binaryQuadraticCode :=
  (octadExteriorWord O).codRestrict binaryQuadraticCode (octadExteriorWord_mem_quadratic O)

theorem octadQuadraticRestriction_surjective (O : Octad) :
    Function.Surjective (octadQuadraticRestriction O) := by
  intro w
  have hw : w.val ∈ (octadExteriorWord O).range := by
    rw [octadExteriorWord_range]
    exact w.property
  obtain ⟨c,hc⟩ := hw
  exact ⟨c,Subtype.ext hc⟩

def octadQuadraticClassMap (O : Octad) : golay →ₗ[Bit] BinaryQuadraticClasses :=
  binaryAffineInQuadratic.mkQ.comp (octadQuadraticRestriction O)

theorem octadExterior_map_shortened (O : Octad) :
    (octadShortenedCode O).map (octadExteriorWord O)=binaryAffineCode := by
  rw [← binaryAffineCodeFour_eq,← octadAffineWord_range O]
  ext w
  constructor
  · rintro ⟨c,hc,he⟩
    exact ⟨⟨c,hc⟩,he⟩
  · rintro ⟨c,hc⟩
    exact ⟨c.val,c.property,hc⟩

/-- The common quotient kernel on the original Golay code. -/
def octadQuadraticKernel (O : Octad) : Submodule Bit golay :=
  octadShortenedCode O ⊔ Submodule.span Bit {octadWord O}

theorem octadQuadraticClassMap_kernel (O : Octad) :
    (octadQuadraticClassMap O).ker=octadQuadraticKernel O := by
  have he : (octadQuadraticClassMap O).ker=binaryAffineCode.comap (octadExteriorWord O) := by
    unfold octadQuadraticClassMap
    rw [LinearMap.ker_comp,Submodule.ker_mkQ]
    rfl
  rw [he,← octadExterior_map_shortened O,Submodule.comap_map_eq,octadExteriorWord_kernel]
  rfl

theorem octadQuadraticClassMap_surjective (O : Octad) :
    Function.Surjective (octadQuadraticClassMap O) :=
  binaryAffineInQuadratic.mkQ_surjective.comp (octadQuadraticRestriction_surjective O)

def octadEvenOne (O : Octad) : octadEvenCode O := octadEvenRestriction O (octadWord O)

def octadEvenConstants (O : Octad) : Submodule Bit (octadEvenCode O) :=
  Submodule.span Bit {octadEvenOne O}

abbrev OctadEvenClasses (O : Octad) := octadEvenCode O ⧸ octadEvenConstants O

def octadEvenClassMap (O : Octad) : golay →ₗ[Bit] OctadEvenClasses O :=
  (octadEvenConstants O).mkQ.comp (octadEvenRestriction O)

theorem octadEvenClassMap_surjective (O : Octad) : Function.Surjective (octadEvenClassMap O) :=
  (octadEvenConstants O).mkQ_surjective.comp (octadEvenRestriction_surjective O)

theorem octadEvenClassMap_kernel (O : Octad) :
    (octadEvenClassMap O).ker=octadQuadraticKernel O := by
  have he : octadEvenConstants O=(Submodule.span Bit {octadWord O}).map (octadEvenRestriction O) := by
    rw [Submodule.map_span,Set.image_singleton]
    rfl
  unfold octadEvenClassMap
  rw [LinearMap.ker_comp,Submodule.ker_mkQ,he,Submodule.comap_map_eq,octadEvenRestriction_kernel]
  exact sup_comm (Submodule.span Bit {octadWord O}) (octadShortenedCode O)

/-- The actual six-dimensional label-space comparison, induced by reading a
single retained Golay word on the octad and on its labelled complement. -/
def octadEvenQuadraticClassesEquiv (O : Octad) :
    OctadEvenClasses O ≃ₗ[Bit] BinaryQuadraticClasses :=
  (LinearMap.quotKerEquivOfSurjective (octadEvenClassMap O)
    (octadEvenClassMap_surjective O)).symm.trans
    ((Submodule.quotEquivOfEq _ _ ((octadEvenClassMap_kernel O).trans
      (octadQuadraticClassMap_kernel O).symm)).trans
      (LinearMap.quotKerEquivOfSurjective (octadQuadraticClassMap O)
        (octadQuadraticClassMap_surjective O)))

end Atlas.Fischer

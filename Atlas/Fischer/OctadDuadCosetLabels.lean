import Atlas.Fischer.OctadDuadFibres
import Atlas.Fischer.ParkerSectionCosets
import Atlas.Fischer.OctadicRootCoordinates

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- The actual shortened word taking a codeword to its literal affine translate. -/
def octadTranslationDifference (O : Octad) (c : golay) (t : BinaryFour) :
    octadShortenedCode O :=
  ⟨octadTranslatedWord O t c-c,by
    rw [← octadEvenRestriction_kernel]
    change octadEvenRestriction O (octadTranslatedWord O t c-c)=0
    rw [map_sub,octadTranslatedWord_inside,sub_self]⟩

theorem octadTranslationDifference_add (O : Octad) (c : golay) (t : BinaryFour) :
    c+(octadTranslationDifference O c t).val=octadTranslatedWord O t c := by
  change c+(octadTranslatedWord O t c-c)=_
  abel

/-- The row/column sign gauge is a literal calibrated Parker coset lift. -/
def octadTranslatedSignedOctad {O : Octad} (Q : OctadCalibration O) (d : SignedOctad)
    (t : BinaryFour) : SignedOctad :=
  ⟨Q.parkerSection.cosetLift d.val (octadTranslationDifference O d.val.1 t),by
    rw [ParkerSection.cosetLift_code,octadTranslationDifference_add,
      octadTranslatedWord_weight]
    exact d.property⟩

theorem octadTranslatedSignedOctad_code {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (t : BinaryFour) :
    (octadTranslatedSignedOctad Q d t).val.1=octadTranslatedWord O t d.val.1 :=
  octadTranslationDifference_add O d.val.1 t

theorem octadTranslatedSignedOctad_injective {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (hd : (support d.val.1.val ∩ O.val).card=2) :
    Function.Injective (octadTranslatedSignedOctad Q d) := by
  intro s t h
  apply octadTranslatedWord_duad_injective O d.val.1 hd
  have he := congrArg (fun e : SignedOctad => e.val.1) h
  simpa only [octadTranslatedSignedOctad_code] using he

end Atlas.Fischer

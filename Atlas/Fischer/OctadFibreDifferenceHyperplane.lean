import Atlas.Fischer.OctadPunctureFibres
import Atlas.Fischer.OctadicRootCoordinates

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev OctadIntersectionFibre (O : Octad) (S : Finset Omega) :=
  {D : Octad // D.val ∩ O.val = S}

/-- The actual sum of two octads in the same intersection fibre is shortened. -/
def octadFibreSum (O : Octad) (S : Finset Omega) (E F : OctadIntersectionFibre O S) :
    octadShortenedCode O :=
  ⟨octadWord E.val + octadWord F.val, by
    rw [← octadEvenRestriction_kernel]
    change octadEvenRestriction O (octadWord E.val + octadWord F.val) = 0
    rw [map_add]
    have he : octadEvenRestriction O (octadWord E.val) =
        octadEvenRestriction O (octadWord F.val) := by
      apply octadEvenRestriction_eq_of_support
      rw [octadWord_support, octadWord_support, E.property, F.property]
    rw [he, ← two_smul Bit, show (2 : Bit) = 0 from rfl, zero_smul]⟩

theorem octadFibreSum_weight (O : Octad) (S : Finset Omega) (E F : OctadIntersectionFibre O S)
    (hEF : (E.val.val ∩ F.val.val).card = 4) :
    hammingNorm (octadFibreSum O S E F).val.val = 8 := by
  have h := binary_weight_add (octadWord E.val).val (octadWord F.val).val
  rw [octadWord_weight, octadWord_weight, overlap_inter, octadWord_support,
    octadWord_support, hEF] at h
  exact (by omega : hammingNorm ((octadWord E.val).val + (octadWord F.val).val) = 8)

def octadFibreSumHyperplane (O : Octad) (S : Finset Omega) (E F : OctadIntersectionFibre O S)
    (hEF : (E.val.val ∩ F.val.val).card = 4) : OctadShortenedHyperplane O :=
  ⟨octadFibreSum O S E F, by
    have hw := octadFibreSum_weight O S E F hEF
    constructor
    · intro h
      rw [h] at hw
      simpa [hammingNorm] using hw
    · intro h
      rw [h] at hw
      have hx := octadComplementWord_weight O
      change hammingNorm (octadShortenedOne O).val.val = 16 at hx
      omega⟩

theorem octadFibreSumHyperplane_overlap (O : Octad) (S : Finset Omega)
    (E F : OctadIntersectionFibre O S) (hEF : (E.val.val ∩ F.val.val).card = 4) :
    overlap (octadWord E.val).val (octadFibreSumHyperplane O S E F hEF).val.val.val = 4 := by
  have he : octadWord E.val + (octadFibreSum O S E F).val = octadWord F.val := by
    change octadWord E.val + (octadWord E.val + octadWord F.val) = _
    rw [← add_assoc, parkerGolay_add_self, zero_add]
  have h := binary_weight_add (octadWord E.val).val (octadFibreSum O S E F).val.val
  have hev := congrArg (fun c : golay => c.val) he
  change (octadWord E.val).val + (octadFibreSum O S E F).val.val = (octadWord F.val).val at hev
  rw [hev, octadWord_weight, octadWord_weight, octadFibreSum_weight O S E F hEF] at h
  exact (by omega : overlap (octadWord E.val).val (octadFibreSum O S E F).val.val = 4)

end Atlas.Fischer

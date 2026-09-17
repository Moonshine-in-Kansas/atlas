import Atlas.Fischer.OctadFibreDifferenceHyperplane

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev OctadFibreRowHyperplanes (O : Octad) (S : Finset Omega) (E : OctadIntersectionFibre O S) :=
  {b : OctadShortenedHyperplane O // overlap (octadWord E.val).val b.val.val.val = 4}

def octadFibreRowWord (O : Octad) (S : Finset Omega) (E : OctadIntersectionFibre O S)
    (b : OctadFibreRowHyperplanes O S E) : golay := octadWord E.val + b.val.val.val

theorem octadFibreRowWord_weight (O : Octad) (S : Finset Omega) (E : OctadIntersectionFibre O S)
    (b : OctadFibreRowHyperplanes O S E) : hammingNorm (octadFibreRowWord O S E b).val = 8 := by
  have h := binary_weight_add (octadWord E.val).val b.val.val.val.val
  rw [octadWord_weight, octadShortenedHyperplane_weight O b.val, b.property] at h
  exact (by omega : hammingNorm ((octadWord E.val).val + b.val.val.val.val) = 8)

def octadFibreRowOctad (O : Octad) (S : Finset Omega) (E : OctadIntersectionFibre O S)
    (b : OctadFibreRowHyperplanes O S E) : Octad :=
  signedOctadSupport ⟨(octadFibreRowWord O S E b, 0), octadFibreRowWord_weight O S E b⟩

theorem octadFibreRowOctad_word (O : Octad) (S : Finset Omega) (E : OctadIntersectionFibre O S)
    (b : OctadFibreRowHyperplanes O S E) :
    octadWord (octadFibreRowOctad O S E b) = octadWord E.val + b.val.val.val := by
  rw [octadFibreRowOctad, octadWord_signedSupport]
  rfl

theorem octadFibreRowOctad_restriction (O : Octad) (S : Finset Omega) (E : OctadIntersectionFibre O S)
    (b : OctadFibreRowHyperplanes O S E) : (octadFibreRowOctad O S E b).val ∩ O.val = S := by
  conv_rhs => rw [← E.property]
  rw [← octadWord_support (octadFibreRowOctad O S E b), octadFibreRowOctad_word]
  ext i
  by_cases hi : i ∈ O.val
  · have hb := (mem_octadShortenedCode O b.val.val.val).mp b.val.val.property i hi
    simp [support, octadWord_apply, hi, hb]
  · simp [hi]

theorem octadFibreRowOctad_ne (O : Octad) (S : Finset Omega) (E : OctadIntersectionFibre O S)
    (b : OctadFibreRowHyperplanes O S E) : octadFibreRowOctad O S E b ≠ E.val := by
  intro h
  have he := congrArg octadWord h
  rw [octadFibreRowOctad_word] at he
  have hz : b.val.val.val = 0 := add_left_cancel (by simpa only [add_zero] using he)
  exact b.val.property.1 (Subtype.ext hz)

/-- Source scalar-branch reindexing, uniform for any actual intersection fibre
whose distinct members meet in four points. -/
def octadFibreRowHyperplaneEquiv (O : Octad) (S : Finset Omega) (E : OctadIntersectionFibre O S)
    (hrow : ∀ F : OctadIntersectionFibre O S, F ≠ E → (E.val.val ∩ F.val.val).card = 4) :
    OctadFibreRowHyperplanes O S E ≃ {F : OctadIntersectionFibre O S // F ≠ E} where
  toFun b := ⟨⟨octadFibreRowOctad O S E b, octadFibreRowOctad_restriction O S E b⟩,
    fun h => octadFibreRowOctad_ne O S E b (congrArg Subtype.val h)⟩
  invFun F := ⟨octadFibreSumHyperplane O S E F.val (hrow F.val F.property),
    octadFibreSumHyperplane_overlap O S E F.val (hrow F.val F.property)⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change octadWord E.val + octadWord (octadFibreRowOctad O S E b) = b.val.val.val
    rw [octadFibreRowOctad_word, ← add_assoc, parkerGolay_add_self, zero_add]
  right_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [← octadWord_support, octadFibreRowOctad_word]
    change support (octadWord E.val + (octadWord E.val + octadWord F.val.val)).val = F.val.val.val
    rw [← add_assoc, parkerGolay_add_self, zero_add, octadWord_support]

end Atlas.Fischer

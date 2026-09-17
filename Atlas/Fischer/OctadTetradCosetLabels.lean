import Atlas.Fischer.OctadTetradPartition
import Atlas.Fischer.ParkerCosetMatrixSigns

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual shortened difference from the chosen tetrad-fibre octad. -/
def octadTetradDifference (O : Octad) (T : Finset Omega) (D E : OctadTetradFibre O T) :
    octadShortenedCode O :=
  ⟨octadWord E.val - octadWord D.val, by
    rw [← octadEvenRestriction_kernel]
    change octadEvenRestriction O (octadWord E.val - octadWord D.val) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply octadEvenRestriction_eq_of_support
    rw [octadWord_support, octadWord_support, E.property, D.property]⟩

theorem octadTetradDifference_add (O : Octad) (T : Finset Omega)
    (D E : OctadTetradFibre O T) :
    octadWord D.val + (octadTetradDifference O T D E).val = octadWord E.val := by
  change octadWord D.val + (octadWord E.val - octadWord D.val) = _
  abel

@[simp] theorem octadTetradDifference_self (O : Octad) (T : Finset Omega)
    (D : OctadTetradFibre O T) : octadTetradDifference O T D D = 0 := by
  apply Subtype.ext
  exact sub_self _

theorem octadTetradDifference_exterior_apply (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D E : OctadTetradFibre O T) (hDE : D ≠ E) (i : Omega)
    (hi : i ∈ octadTetradExterior O T D) :
    (octadTetradDifference O T D E).val.val i = 1 := by
  have hd := Finset.mem_sdiff.mp hi
  have he : i ∉ E.val.val := by
    intro he
    exact Finset.disjoint_left.mp (octadTetradExterior_disjoint O T hT D E hDE)
      hi (Finset.mem_sdiff.mpr ⟨he, hd.2⟩)
  change (octadWord E.val).val i - (octadWord D.val).val i = 1
  rw [octadWord_apply, octadWord_apply, ite_eq_right he, ite_eq_left hd.1]
  decide

/-- All Parker matrix signs in the four-point tetrad fibre vanish in the
actual calibrated coset gauge, because its exterior tetrads are disjoint. -/
theorem octadTetradDifference_triple_zero (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D E F : OctadTetradFibre O T) :
    parkerTripleIntersection (octadWord D.val).val
      (octadTetradDifference O T D E).val.val (octadTetradDifference O T D F).val.val = 0 := by
  by_cases he : D = E
  · subst E
    simp [parkerTripleIntersection]
  by_cases hf : D = F
  · subst F
    simp [parkerTripleIntersection]
  have hp (i : Omega) : (octadWord D.val).val i *
      (octadTetradDifference O T D E).val.val i *
      (octadTetradDifference O T D F).val.val i =
      if i ∈ octadTetradExterior O T D then (1 : Bit) else 0 := by
    by_cases hi : i ∈ octadTetradExterior O T D
    · rw [ite_eq_left hi, octadTetradDifference_exterior_apply O T hT D E he i hi,
        octadTetradDifference_exterior_apply O T hT D F hf i hi,
        octadWord_apply, ite_eq_left (Finset.mem_sdiff.mp hi).1]
      norm_num
    · rw [ite_eq_right hi]
      by_cases ho : i ∈ O.val
      · have hz := (mem_octadShortenedCode O (octadTetradDifference O T D E).val).mp
          (octadTetradDifference O T D E).property i ho
        rw [hz, mul_zero, zero_mul]
      · have hd : i ∉ D.val.val := fun hd => hi (Finset.mem_sdiff.mpr ⟨hd, ho⟩)
        rw [octadWord_apply, ite_eq_right hd, zero_mul, zero_mul]
  simp only [parkerTripleIntersection, hp, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
    octadTetradExterior_card O T hT]
  decide

def octadTetradSignedLabel {O : Octad} (Q : OctadCalibration O) (T : Finset Omega)
    (D E : OctadTetradFibre O T) : SignedOctad :=
  ⟨Q.parkerSection.cosetLift (canonicalOctadLift D.val).val (octadTetradDifference O T D E), by
    rw [ParkerSection.cosetLift_code]
    change hammingNorm (octadWord D.val + (octadTetradDifference O T D E).val).val = 8
    rw [octadTetradDifference_add]
    exact octadWord_weight E.val⟩

theorem octadTetradSignedLabel_code {O : Octad} (Q : OctadCalibration O) (T : Finset Omega)
    (D E : OctadTetradFibre O T) : (octadTetradSignedLabel Q T D E).val.1 = octadWord E.val :=
  octadTetradDifference_add O T D E

theorem octadTetradSignedLabel_support {O : Octad} (Q : OctadCalibration O) (T : Finset Omega)
    (D E : OctadTetradFibre O T) : signedOctadSupport (octadTetradSignedLabel Q T D E) = E.val := by
  apply Subtype.ext
  change support (octadTetradSignedLabel Q T D E).val.1.val = E.val.val
  rw [octadTetradSignedLabel_code, octadWord_support]

/-- Exact row-to-column multiplication, with the Parker sign proved to be zero. -/
theorem octadTetradSignedLabel_multiply {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D E F : OctadTetradFibre O T) :
    parkerLoopMultiply (octadTetradSignedLabel Q T D E).val
      (Q.parkerSection.lift (octadTetradDifference O T D E + octadTetradDifference O T D F)) =
      (octadTetradSignedLabel Q T D F).val := by
  change parkerLoopMultiply (Q.parkerSection.cosetLift (canonicalOctadLift D.val).val _)
    (Q.parkerSection.lift _) = _
  rw [ParkerSection.cosetLift_matrix_sign]
  change parkerSign (parkerTripleIntersection (octadWord D.val).val
    (octadTetradDifference O T D E).val.val (octadTetradDifference O T D F).val.val) _ = _
  rw [octadTetradDifference_triple_zero O T hT, parkerSign_zero]
  rfl


/-- The same actual gauge with any signed base, needed for its complementary lift. -/
def octadTetradCosetLabel {O : Octad} (Q : OctadCalibration O) (T : Finset Omega)
    (D : OctadTetradFibre O T) (d : ParkerLoop) (hd : d.1 = octadWord D.val)
    (E : OctadTetradFibre O T) : SignedOctad :=
  ⟨Q.parkerSection.cosetLift d (octadTetradDifference O T D E), by
    rw [ParkerSection.cosetLift_code, hd, octadTetradDifference_add]
    exact octadWord_weight E.val⟩

theorem octadTetradCosetLabel_code {O : Octad} (Q : OctadCalibration O) (T : Finset Omega)
    (D : OctadTetradFibre O T) (d : ParkerLoop) (hd : d.1 = octadWord D.val)
    (E : OctadTetradFibre O T) : (octadTetradCosetLabel Q T D d hd E).val.1 = octadWord E.val := by
  change d.1 + (octadTetradDifference O T D E).val = _
  rw [hd, octadTetradDifference_add]

theorem octadTetradCosetLabel_support {O : Octad} (Q : OctadCalibration O) (T : Finset Omega)
    (D : OctadTetradFibre O T) (d : ParkerLoop) (hd : d.1 = octadWord D.val)
    (E : OctadTetradFibre O T) : signedOctadSupport (octadTetradCosetLabel Q T D d hd E) = E.val := by
  apply Subtype.ext
  change support (octadTetradCosetLabel Q T D d hd E).val.1.val = E.val.val
  rw [octadTetradCosetLabel_code, octadWord_support]

theorem octadTetradCosetLabel_multiply {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (E F : OctadTetradFibre O T) :
    parkerLoopMultiply (octadTetradCosetLabel Q T D d hd E).val
      (Q.parkerSection.lift (octadTetradDifference O T D E + octadTetradDifference O T D F)) =
      (octadTetradCosetLabel Q T D d hd F).val := by
  change parkerLoopMultiply (Q.parkerSection.cosetLift d _) (Q.parkerSection.lift _) = _
  have ht : parkerTripleIntersection d.1.val (octadTetradDifference O T D E).val.val
      (octadTetradDifference O T D F).val.val = 0 := by
    rw [hd]
    exact octadTetradDifference_triple_zero O T hT D E F
  rw [ParkerSection.cosetLift_matrix_sign, ht, parkerSign_zero]
  rfl

end Atlas.Fischer


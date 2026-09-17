import Atlas.Fischer.OctadicCalibratedProducts
import Atlas.Fischer.OctadHyperplanePairs

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem calibratedOctad_commutes_hyperplane {O : Octad} (Q : OctadCalibration O)
    (c : OctadShortenedHyperplane O) :
    parkerLoopMultiply Q.octadLift.val (Q.parkerSection.lift c.val) =
      parkerLoopMultiply (Q.parkerSection.lift c.val) Q.octadLift.val := by
  have hh : golayHalfOverlap Q.octadLift.val.1 (Q.parkerSection.lift c.val).1 = 0 := by
    unfold golayHalfOverlap
    change ((overlap Q.octadLift.val.1.val (calibratedHyperplaneLift Q c).val.1.val / 2 : ℕ) : Bit) = 0
    rw [← signedOctadIntersection_overlap Q.octadLift (calibratedHyperplaneLift Q c),
      calibrated_octad_hyperplane_disjoint]
    norm_num
  rw [parkerLoopMultiply_commutator, hh, parkerSign_zero]

theorem calibratedOctad_associates_hyperplane_right {O : Octad} (Q : OctadCalibration O)
    (x : ParkerLoop) (c : OctadShortenedHyperplane O) :
    parkerLoopMultiply (parkerLoopMultiply x (Q.parkerSection.lift c.val)) Q.octadLift.val =
      parkerLoopMultiply x (parkerLoopMultiply (Q.parkerSection.lift c.val) Q.octadLift.val) := by
  have ht : parkerTripleIntersection x.1 (Q.parkerSection.lift c.val).1 Q.octadLift.val.1 = 0 := by
    unfold parkerTripleIntersection
    apply Finset.sum_eq_zero
    intro i hi
    change x.1.val i * c.val.val.val i * Q.octadLift.val.1.val i = 0
    by_cases ho : i ∈ O.val
    · have hz := (mem_octadShortenedCode O c.val.val).mp c.val.property i ho
      rw [hz, mul_zero, zero_mul]
    · rw [Q.lift_code, octadWord_apply, ite_eq_right ho, mul_zero]
  rw [parkerLoopMultiply_associator, ht, parkerSign_zero]

theorem calibratedSection_complement_label {O : Octad} (Q : OctadCalibration O)
    (c : OctadShortenedHyperplane O) :
    Q.parkerSection.lift (octadHyperplaneComplement O c).val =
      parkerLoopMultiply (parkerLoopMultiply Q.octadLift.val (Q.parkerSection.lift c.val)) parkerOmega := by
  have h := congrArg Subtype.val
    (calibrated_mixed_label Q c (octadHyperplaneComplement O c) (add_comm _ _))
  exact h.symm

/-- The disjoint source label at the complementary hyperplane is exactly the
four-intersection label followed by o. All associator signs are proved zero. -/
theorem calibratedComplement_product_label {O : Octad} (Q : OctadCalibration O)
    (x : ParkerLoop) (c : OctadShortenedHyperplane O) :
    parkerLoopMultiply (parkerLoopMultiply x
      (Q.parkerSection.lift (octadHyperplaneComplement O c).val)) parkerOmega =
      parkerLoopMultiply (parkerLoopMultiply x (Q.parkerSection.lift c.val)) Q.octadLift.val := by
  rw [calibratedSection_complement_label,
    ← parkerOmega_associates_right x (parkerLoopMultiply Q.octadLift.val (Q.parkerSection.lift c.val)),
    parkerOmega_associates_middle, parkerOmega_square, parkerLoopMultiply_one_right,
    calibratedOctad_commutes_hyperplane, ← calibratedOctad_associates_hyperplane_right]

end Atlas.Fischer

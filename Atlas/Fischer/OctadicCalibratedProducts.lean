import Atlas.Fischer.OctadicRootCoordinates
import Atlas.Fischer.SignedOctadProductFormulas

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

 theorem calibrated_octad_hyperplane_disjoint {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    signedOctadIntersection Q.octadLift (calibratedHyperplaneLift Q b) = 0 := by
  classical
  rw [signedOctadIntersection_overlap]
  change overlap Q.octadLift.val.1.val b.val.val.val=0
  rw [Q.lift_code,overlap_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ O.val
  · have hz := (mem_octadShortenedCode O b.val.val).mp b.val.property i hi
    simp [hz]
  · simp [octadWord_apply,hi]

/-- The actual product label has positive sign in the Ω-calibrated section. -/
theorem calibrated_mixed_label {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) (hc : c.val=octadShortenedOne O+b.val) :
    octadProductDisjoint Q.octadLift (calibratedHyperplaneLift Q b)
      (calibrated_octad_hyperplane_disjoint Q b) = calibratedHyperplaneLift Q c := by
  apply Subtype.ext
  change parkerLoopMultiply (parkerLoopMultiply Q.octadLift.val (Q.parkerSection.lift b.val))
    parkerOmega = Q.parkerSection.lift c.val
  rw [← parkerOmega_commutes,← parkerOmega_associates_left,← Q.calibrated,
    ← Q.parkerSection.lift_multiply,← hc]

theorem product_calibrated_octad_hyperplane {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) (hc : c.val=octadShortenedOne O+b.val) :
    (2 : Scalar) • product (signedOctadVector Q.octadLift) (calibratedHyperplaneVector Q b) =
      theta • calibratedHyperplaneVector Q c := by
  change (2 : Scalar) • product (signedOctadVector Q.octadLift)
    (signedOctadVector (calibratedHyperplaneLift Q b)) = _
  rw [product_signedOctads_disjoint _ _ (calibrated_octad_hyperplane_disjoint Q b),
    calibrated_mixed_label Q b c hc]
  rfl

/-- Conjugating θ in the first input supplies the sign yielding source row five. -/
theorem product_theta_octad_hyperplane {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) (hc : c.val=octadShortenedOne O+b.val) :
    (2 : Scalar) • product (theta • signedOctadVector Q.octadLift)
      (calibratedHyperplaneVector Q b) = (3 : Scalar) • calibratedHyperplaneVector Q c := by
  rw [product_smul_left]
  calc
    _ = star theta • ((2 : Scalar) • product (signedOctadVector Q.octadLift)
        (calibratedHyperplaneVector Q b)) := by module
    _ = _ := by
      rw [product_calibrated_octad_hyperplane Q b c hc,smul_smul]
      congr 1
      rw [theta_conjugate,neg_mul,← pow_two,theta_sq]
      ring

 theorem calibrated_hyperplanes_intersection_four {O : Octad} (Q : OctadCalibration O)
    (b c d : OctadShortenedHyperplane O) (hd : b.val+c.val=d.val) :
    signedOctadIntersection (calibratedHyperplaneLift Q b) (calibratedHyperplaneLift Q c)=4 := by
  rw [signedOctadIntersection_overlap]
  have h := binary_weight_add b.val.val.val c.val.val.val
  have he : b.val.val.val+c.val.val.val=d.val.val.val := congrArg (fun a : octadShortenedCode O => a.val.val) hd
  rw [he,octadShortenedHyperplane_weight O b,octadShortenedHyperplane_weight O c,
    octadShortenedHyperplane_weight O d] at h
  change overlap b.val.val.val c.val.val.val=4
  omega

theorem product_calibrated_hyperplanes_four {O : Octad} (Q : OctadCalibration O)
    (b c d : OctadShortenedHyperplane O) (hd : b.val+c.val=d.val) :
    (2 : Scalar) • product (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q c) =
      calibratedHyperplaneVector Q d := by
  have he : octadProductFour (calibratedHyperplaneLift Q b) (calibratedHyperplaneLift Q c)
      (calibrated_hyperplanes_intersection_four Q b c d hd) = calibratedHyperplaneLift Q d := by
    apply Subtype.ext
    change parkerLoopMultiply (Q.parkerSection.lift b.val) (Q.parkerSection.lift c.val) = _
    rw [← Q.parkerSection.lift_multiply,hd]
    rfl
  change (2 : Scalar) • product (signedOctadVector _) (signedOctadVector _) = _
  rw [product_signedOctads_four _ _ (calibrated_hyperplanes_intersection_four Q b c d hd),he]
  rfl

theorem calibrated_hyperplanes_disjoint {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) (hc : b.val+c.val=octadShortenedOne O) :
    signedOctadIntersection (calibratedHyperplaneLift Q b) (calibratedHyperplaneLift Q c)=0 := by
  rw [signedOctadIntersection_overlap]
  have h := binary_weight_add b.val.val.val c.val.val.val
  have he : b.val.val.val+c.val.val.val=(octadComplementWord O).val :=
    congrArg (fun a : octadShortenedCode O => a.val.val) hc
  rw [he,octadShortenedHyperplane_weight O b,octadShortenedHyperplane_weight O c,
    octadComplementWord_weight] at h
  change overlap b.val.val.val c.val.val.val=0
  omega

theorem product_calibrated_hyperplanes_complement {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) (hc : b.val+c.val=octadShortenedOne O) :
    (2 : Scalar) • product (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q c) =
      theta • signedOctadVector Q.octadLift := by
  have he : octadProductDisjoint (calibratedHyperplaneLift Q b) (calibratedHyperplaneLift Q c)
      (calibrated_hyperplanes_disjoint Q b c hc) = Q.octadLift := by
    apply Subtype.ext
    change parkerLoopMultiply (parkerLoopMultiply (Q.parkerSection.lift b.val)
      (Q.parkerSection.lift c.val)) parkerOmega = Q.octadLift.val
    rw [← Q.parkerSection.lift_multiply,hc,Q.calibrated,parkerOmega_associates_left,
      ← parkerOmega_commutes Q.octadLift.val,← parkerOmega_associates_left,parkerOmega_square,
      parkerLoopMultiply_one_left]
  change (2 : Scalar) • product (signedOctadVector _) (signedOctadVector _) = _
  rw [product_signedOctads_disjoint _ _ (calibrated_hyperplanes_disjoint Q b c hc),he]

end Atlas.Fischer

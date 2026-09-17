import Atlas.Fischer.CalibratedComplementLabels

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The marked octad is disjoint from every word of its actual shortened code. -/
theorem calibratedShortened_triple_zero {O : Octad} (Q : OctadCalibration O)
    (x : ParkerLoop) (b : octadShortenedCode O) :
    parkerTripleIntersection x.1 Q.octadLift.val.1 (Q.parkerSection.lift b).1 = 0 := by
  unfold parkerTripleIntersection
  apply Finset.sum_eq_zero
  intro i hi
  change x.1.val i * Q.octadLift.val.1.val i * b.val.val i = 0
  by_cases ho : i ∈ O.val
  · have hz := (mem_octadShortenedCode O b.val).mp b.property i ho
    rw [hz, mul_zero]
  · rw [Q.lift_code, octadWord_apply, ite_eq_right ho, mul_zero, zero_mul]

theorem calibratedShortened_commutes {O : Octad} (Q : OctadCalibration O)
    (b : octadShortenedCode O) :
    parkerLoopMultiply Q.octadLift.val (Q.parkerSection.lift b) =
      parkerLoopMultiply (Q.parkerSection.lift b) Q.octadLift.val := by
  have hz : overlap Q.octadLift.val.1.val b.val.val = 0 := by
    unfold overlap
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    by_cases ho : i ∈ O.val
    · exact h.2 ((mem_octadShortenedCode O b.val).mp b.property i ho)
    · apply h.1
      rw [Q.lift_code, octadWord_apply, ite_eq_right ho]
  have hh : golayHalfOverlap Q.octadLift.val.1 (Q.parkerSection.lift b).1 = 0 := by
    change ((overlap Q.octadLift.val.1.val b.val.val / 2 : ℕ) : Bit) = 0
    rw [hz]
    norm_num
  rw [parkerLoopMultiply_commutator, hh, parkerSign_zero]

/-- Transport the actual coset label across multiplication by the marked octad. -/
theorem calibratedShortened_coset_right {O : Octad} (Q : OctadCalibration O)
    (x : ParkerLoop) (b : octadShortenedCode O) :
    parkerLoopMultiply (parkerLoopMultiply x Q.octadLift.val) (Q.parkerSection.lift b) =
      parkerLoopMultiply (parkerLoopMultiply x (Q.parkerSection.lift b)) Q.octadLift.val := by
  have hs : parkerTripleIntersection x.1 (Q.parkerSection.lift b).1 Q.octadLift.val.1 = 0 := by
    rw [parkerTripleIntersection_swap]
    exact calibratedShortened_triple_zero Q x b
  rw [parkerLoopMultiply_associator, calibratedShortened_triple_zero, parkerSign_zero,
    calibratedShortened_commutes, parkerLoopMultiply_associator, hs, parkerSign_zero]

theorem calibratedOctad_square {O : Octad} (Q : OctadCalibration O) :
    parkerLoopMultiply Q.octadLift.val Q.octadLift.val = (0, 0) := by
  rw [parkerLoopMultiply_square]
  congr 1
  unfold golayQuarterWeight
  rw [Q.octadLift.property]
  norm_num
  decide

theorem calibratedOctad_right_involutive {O : Octad} (Q : OctadCalibration O)
    (x : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply x Q.octadLift.val) Q.octadLift.val = x := by
  rw [parkerLoopMultiply_associator, parkerTripleIntersection_repeat, parkerSign_zero,
    calibratedOctad_square, parkerLoopMultiply_one_right]

end Atlas.Fischer

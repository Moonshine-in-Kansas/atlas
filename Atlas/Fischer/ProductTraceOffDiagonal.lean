import Atlas.Fischer.ProductTraceCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem productTraceCoordinateWord_weight_le (i : CoordinateIndex) :
    hammingNorm (productTraceCoordinateWord i).val ≤ 8 := by
  cases i with
  | inl i => simp [productTraceCoordinateWord,hammingNorm_zero]
  | inr O => exact (octadWord_weight O).le

theorem productTraceCoordinateWord_sum_ne_one (i j : CoordinateIndex) :
    productTraceCoordinateWord i + productTraceCoordinateWord j ≠ golayOne := by
  intro h
  have hw := binary_weight_add (productTraceCoordinateWord i).val (productTraceCoordinateWord j).val
  have hv : hammingNorm ((productTraceCoordinateWord i).val +
      (productTraceCoordinateWord j).val)=24 := by
    change hammingNorm ((productTraceCoordinateWord i + productTraceCoordinateWord j).val)=24
    rw [h]
    exact (weight_twentyfour_iff _).mpr rfl
  have hi := productTraceCoordinateWord_weight_le i
  have hj := productTraceCoordinateWord_weight_le j
  omega

/-- All distinct coordinate characters give orthogonal multiplication slices. -/
theorem productTrace_coordinate_vanish (i j : CoordinateIndex)
    (hij : productTraceCoordinateWord i ≠ productTraceCoordinateWord j) :
    productTrace (coordinateVector i) (coordinateVector j)=0 := by
  apply productTrace_coordinate_vanish_of_labels
  · intro h
    have he := congrArg (fun c : golay => c + productTraceCoordinateWord j) h
    rw [add_assoc,parkerGolay_add_self,add_zero,zero_add] at he
    exact hij he
  · exact productTraceCoordinateWord_sum_ne_one i j

theorem productTrace_octad_point_zero (O : Octad) (i : Omega) :
    productTrace (coordinateVector (Sum.inr O)) (coordinateVector (Sum.inl i))=0 := by
  apply productTrace_coordinate_vanish
  intro h
  have hw := congrArg (fun c : golay => hammingNorm c.val) h
  change hammingNorm (octadWord O).val = hammingNorm (0 : BinaryWord) at hw
  rw [octadWord_weight,hammingNorm_zero] at hw
  omega

theorem productTrace_point_octad_zero (i : Omega) (O : Octad) :
    productTrace (coordinateVector (Sum.inl i)) (coordinateVector (Sum.inr O))=0 := by
  apply productTrace_coordinate_vanish
  intro h
  have hw := congrArg (fun c : golay => hammingNorm c.val) h
  change hammingNorm (0 : BinaryWord) = hammingNorm (octadWord O).val at hw
  rw [octadWord_weight,hammingNorm_zero] at hw
  omega

theorem productTrace_distinct_octads_zero (O P : Octad) (hOP : O ≠ P) :
    productTrace (coordinateVector (Sum.inr O)) (coordinateVector (Sum.inr P))=0 := by
  apply productTrace_coordinate_vanish
  exact fun h => hOP (octadWord_injective h)

end Atlas.Fischer

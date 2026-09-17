import Atlas.Fischer.WeightedCubicTensor
import Atlas.Fischer.CubicSliceIncidence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def cubicPointPattern (i a b : Omega) : Scalar :=
  if a=b then (if i=a then -81 else 15) else if i=a ∨ i=b then 15 else -1

theorem coordinateCubic_points (i a b : Omega) :
    coordinateCubic (.inl i) (.inl a) (.inl b)=cubicPointPattern i a b/1024 := by
  rw [coordinateCubic,cubic,product_coordinateVector,hermitian_coordinateVector_left]
  simp only [basisProduct,coordinateWeight,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  change (1/8 : Scalar)*star (axisBasisProduct a b (.inl i))=_
  rw [axisBasisProduct_axis_apply]
  unfold cubicPointPattern
  split_ifs <;> norm_num

theorem coordinateCubic_two_points_octad (i a : Omega) (D : Octad) :
    coordinateCubic (.inl i) (.inl a) (.inr D)=0 := by
  simp [coordinateCubic,cubic,product_coordinateVector,hermitian_coordinateVector_left,basisProduct]

theorem coordinateCubic_point_octads (i : Omega) (D E : Octad) :
    coordinateCubic (.inl i) (.inr D) (.inr E)=
      if D=E then cubicPointOctadIncidence i D/16 else 0 := by
  rw [coordinateCubic,cubic,product_coordinateVector,hermitian_coordinateVector_left]
  simp only [basisProduct,coordinateWeight,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  change (1/8 : Scalar)*star (octadBasisProduct D E (.inl i))=_
  rw [octadBasisProduct_axis_apply]
  by_cases h : D=E
  · subst E
    simp only [ite_true,cubicPointOctadIncidence]
    split_ifs <;> norm_num
  · simp [h]

theorem cubicPointPattern_star (i a b : Omega) : star (cubicPointPattern i a b)=cubicPointPattern i a b := by
  unfold cubicPointPattern
  split_ifs <;> norm_num

theorem cubicPointOctadIncidence_star (i : Omega) (D : Octad) :
    star (cubicPointOctadIncidence i D)=cubicPointOctadIncidence i D := by
  unfold cubicPointOctadIncidence
  split_ifs <;> norm_num

end Atlas.Fischer

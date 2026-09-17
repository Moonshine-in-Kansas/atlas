import Atlas.Fischer.OctadicFortySixBlock

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem rootMap_sub (r x y : Coordinates) : rootMap r (x - y) = rootMap r x - rootMap r y :=
  map_sub (rootMapSemilinear r) x y

def octadicDifferencePairVector {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) : Coordinates :=
  calibratedHyperplaneVector Q b - calibratedHyperplaneVector Q (octadHyperplaneComplement O b)

theorem octadicHyperplaneAxisVector_complement {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    octadicHyperplaneAxisVector Q (octadHyperplaneComplement O b) = -octadicHyperplaneAxisVector Q b := by
  have hn := octadHyperplaneComplement_ne O b
  have hh : hermitian (octadicHyperplaneAxisVector Q b +
      octadicHyperplaneAxisVector Q (octadHyperplaneComplement O b))
    (octadicHyperplaneAxisVector Q b + octadicHyperplaneAxisVector Q (octadHyperplaneComplement O b)) = 0 := by
    simp only [hermitian_add_left, hermitian_add_right, hermitian_hyperplaneAxisVector,
      ite_eq_left rfl, ite_eq_right hn, ite_eq_right (Ne.symm hn),
      octadHyperplaneComplement_involutive O b]
    norm_num
  have h := (hermitian_self_eq_zero _).mp hh
  exact eq_neg_of_add_eq_zero_right h

theorem octadicComplementPairVector_complement {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    octadicComplementPairVector Q (octadHyperplaneComplement O b) = octadicComplementPairVector Q b := by
  simp only [octadicComplementPairVector, octadHyperplaneComplement_involutive O b]
  exact add_comm _ _

theorem rootMap_octadic_hyperplane_split {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    rootMap (octadicRoot Q 0) (calibratedHyperplaneVector Q b) =
      (1 / 2 : Scalar) • (octadicHyperplaneAxisVector Q b + octadicComplementPairVector Q b) := by
  rw [rootMap_octadic_hyperplane]
  unfold octadicHyperplaneAxisVector octadicComplementPairVector
  rw [add_assoc]

/-- The fifteen complementary-pair sums are actual fixed vectors. -/
theorem rootMap_octadic_complementPair_fixed {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    rootMap (octadicRoot Q 0) (octadicComplementPairVector Q b) = octadicComplementPairVector Q b := by
  rw [octadicComplementPairVector, rootMap_add, rootMap_octadic_hyperplane_split,
    rootMap_octadic_hyperplane_split, octadicHyperplaneAxisVector_complement,
    octadicComplementPairVector_complement]
  change _ = octadicComplementPairVector Q b
  module

/-- One direction of each actual two-dimensional swap block. -/
theorem rootMap_octadic_differencePair {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    rootMap (octadicRoot Q 0) (octadicDifferencePairVector Q b) = octadicHyperplaneAxisVector Q b := by
  rw [octadicDifferencePairVector, rootMap_sub, rootMap_octadic_hyperplane_split,
    rootMap_octadic_hyperplane_split, octadicHyperplaneAxisVector_complement,
    octadicComplementPairVector_complement]
  module

/-- The reverse swap follows from the verified involution on the same actual block. -/
theorem rootMap_octadic_hyperplaneAxisVector {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    rootMap (octadicRoot Q 0) (octadicHyperplaneAxisVector Q b) = octadicDifferencePairVector Q b := by
  have hy (c : OctadShortenedHyperplane O) :
      calibratedHyperplaneVector Q c ∈ octadicFortySixSpace Q :=
    Submodule.subset_span (Or.inr ⟨c, rfl⟩)
  have hd : octadicDifferencePairVector Q b ∈ octadicFortySixSpace Q :=
    (octadicFortySixSpace Q).sub_mem (hy b) (hy _)
  rw [← rootMap_octadic_differencePair Q b]
  exact rootMap_octadic_fortySix_involutive Q _ hd

theorem octadicHyperplaneAxisVector_norm {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (octadicHyperplaneAxisVector Q b) (octadicHyperplaneAxisVector Q b) = 2 := by
  rw [hermitian_hyperplaneAxisVector, ite_eq_left rfl]

theorem octadicComplementPairVector_norm {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (octadicComplementPairVector Q b) (octadicComplementPairVector Q b) = 2 := by
  rw [hermitian_complementPairVector, ite_eq_left rfl]

theorem octadicDifferencePairVector_norm {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (octadicDifferencePairVector Q b) (octadicDifferencePairVector Q b) = 2 := by
  have hn := octadHyperplaneComplement_ne O b
  simp only [octadicDifferencePairVector, hermitian_sub_left, hermitian_sub_right,
    calibratedHyperplaneVector_orthonormal, ite_eq_left rfl, ite_eq_right hn,
    ite_eq_right (Ne.symm hn)]
  norm_num

end Atlas.Fischer

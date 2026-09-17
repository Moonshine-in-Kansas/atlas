import Atlas.Fischer.OctadicExteriorPairings

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def octadicComplementPairVector {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) : Coordinates :=
  calibratedHyperplaneVector Q b + calibratedHyperplaneVector Q (octadHyperplaneComplement O b)

theorem hermitian_complementPairVector {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) :
    hermitian (octadicComplementPairVector Q b) (octadicComplementPairVector Q c) =
      if b = c then 2 else if c = octadHyperplaneComplement O b then 2 else 0 := by
  have hn (d : OctadShortenedHyperplane O) : d ≠ octadHyperplaneComplement O d :=
    Ne.symm (octadHyperplaneComplement_ne O d)
  have hi (d : OctadShortenedHyperplane O) :
      octadHyperplaneComplement O (octadHyperplaneComplement O d) = d :=
    octadHyperplaneComplement_involutive O d
  by_cases hbc : b = c
  · subst c
    simp [octadicComplementPairVector, hermitian_add_left, hermitian_add_right,
      calibratedHyperplaneVector_orthonormal, hn, octadHyperplaneComplement_ne]
    norm_num
  · by_cases hc : c = octadHyperplaneComplement O b
    · subst c
      simp [octadicComplementPairVector, hermitian_add_left, hermitian_add_right,
        calibratedHyperplaneVector_orthonormal, hn, octadHyperplaneComplement_ne,
        hi]
      norm_num
    · have hbc' : b ≠ octadHyperplaneComplement O c := by
        intro h
        apply hc
        have hh := congrArg (octadHyperplaneComplement O) h
        simpa only [hi] using hh.symm
      have hcc : octadHyperplaneComplement O b ≠ octadHyperplaneComplement O c :=
        fun h => hbc ((octadHyperplaneComplement_involutive O).injective h)
      simp only [octadicComplementPairVector, hermitian_add_left, hermitian_add_right,
        calibratedHyperplaneVector_orthonormal, ite_eq_right hbc, ite_eq_right hc,
        ite_eq_right hbc', ite_eq_right (Ne.symm hc), ite_eq_right hcc]
      ring

theorem hermitian_hyperplaneAxisVector_signedOctad {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) (d : SignedOctad) :
    hermitian (octadicHyperplaneAxisVector Q b) (signedOctadVector d) = 0 := by
  simp only [octadicHyperplaneAxisVector, octadicHyperplaneAxisSum,
    hermitian_sub_left, hermitian_smul_left, hermitian_octadAxisSum_signedOctad,
    octadExteriorAxisSum, hermitian_sum_left, hermitian_u_signedOctad,
    Finset.sum_const_zero, mul_zero, sub_self]

theorem hermitian_hyperplaneAxisVector_complementPair {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) :
    hermitian (octadicHyperplaneAxisVector Q b) (octadicComplementPairVector Q c) = 0 := by
  simp only [octadicComplementPairVector, hermitian_add_right, calibratedHyperplaneVector,
    hermitian_hyperplaneAxisVector_signedOctad, add_zero]

theorem rootMap_octadic_hyperplane_pairing {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) :
    hermitian (rootMap (octadicRoot Q 0) (calibratedHyperplaneVector Q b))
      (rootMap (octadicRoot Q 0) (calibratedHyperplaneVector Q c)) =
      star (hermitian (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q c)) := by
  have hr (d : OctadShortenedHyperplane O) :
      rootMap (octadicRoot Q 0) (calibratedHyperplaneVector Q d) =
        (1 / 2 : Scalar) • (octadicHyperplaneAxisVector Q d + octadicComplementPairVector Q d) := by
    rw [rootMap_octadic_hyperplane]
    unfold octadicHyperplaneAxisVector octadicComplementPairVector
    rw [add_assoc]
  rw [hr, hr]
  have hz : hermitian (octadicComplementPairVector Q b) (octadicHyperplaneAxisVector Q c) = 0 := by
    rw [← hermitian_star, hermitian_hyperplaneAxisVector_complementPair, star_zero]
  simp only [hermitian_smul_left, hermitian_smul_right, hermitian_add_left,
    hermitian_add_right, hermitian_hyperplaneAxisVector_complementPair, hz,
    hermitian_complementPairVector, hermitian_hyperplaneAxisVector,
    calibratedHyperplaneVector_orthonormal]
  split_ifs <;> norm_num

end Atlas.Fischer

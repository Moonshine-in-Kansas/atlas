import Atlas.Fischer.CoordinateEvaluation
import Atlas.Fischer.OctadCubicSigns

namespace Atlas.Fischer
open Atlas.Codes

theorem signedOctadSupport_canonical (O : Octad) :
    signedOctadSupport (canonicalOctadLift O) = O := by
  apply Subtype.ext
  exact octadWord_support O

theorem octadIntersection_self (O : Octad) :
    signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift O) = 8 := by
  simp only [signedOctadIntersection, signedOctadSupport_canonical, Finset.inter_self]
  exact octad_size O.val O.prop

/-- The octad-coordinate tensor is sparse by the actual code equations,
not by an externally supplied list of tensor entries. -/
theorem octadBasisProduct_octad_apply (A B C : Octad) :
    octadBasisProduct B C (Sum.inr A) =
      if octadWord A = octadWord B + octadWord C then
        (1 / 2 : Scalar) * parkerScalarSign (parkerGolayFactorSet (octadWord B) (octadWord C))
      else if octadWord A = octadWord B + octadWord C + golayOne then
        (theta / 2 : Scalar) * parkerScalarSign
          (parkerGolayFactorSet (octadWord B) (octadWord C) +
            parkerGolayFactorSet (octadWord B + octadWord C) golayOne)
      else 0 := by
  classical
  by_cases he : B = C
  · subst C
    have hn : ¬octadWord A = octadWord B + octadWord B := by
      intro h
      have hh := octadWord_sum_weight A B B h
      rw [octadIntersection_self] at hh
      omega
    have hn' : ¬octadWord A = octadWord B + octadWord B + golayOne := by
      intro h
      have hh := octadWord_complementary_sum_weight A B B h
      rw [octadIntersection_self] at hh
      omega
    simp [octadBasisProduct, hn, hn']
  · unfold octadBasisProduct
    rw [if_neg he]
    by_cases h4 : signedOctadIntersection (canonicalOctadLift B) (canonicalOctadLift C) = 4
    · have hn' : ¬octadWord A = octadWord B + octadWord C + golayOne := by
        intro h
        have hh := octadWord_complementary_sum_weight A B C h
        omega
      rw [dif_pos h4]
      simp [signedOctadVector_octad_apply, octadProductFour, canonicalOctadLift,
        parkerLoopMultiply, parkerMultiply, hn', mul_ite]
    · rw [dif_neg h4]
      have hn : ¬octadWord A = octadWord B + octadWord C := by
        intro h
        exact h4 (octadWord_sum_weight A B C h)
      by_cases h0 : signedOctadIntersection (canonicalOctadLift B) (canonicalOctadLift C) = 0
      · rw [dif_pos h0]
        simp [signedOctadVector_octad_apply, octadProductDisjoint, canonicalOctadLift,
          parkerLoopMultiply, parkerMultiply, hn, mul_ite]
      · have hn' : ¬octadWord A = octadWord B + octadWord C + golayOne := by
          intro h
          exact h0 (octadWord_complementary_sum_weight A B C h)
        rw [dif_neg h0]
        simp [hn, hn']

theorem octad_sum_switch (A B C : Octad) :
    octadWord A = octadWord B + octadWord C ↔
      octadWord B = octadWord A + octadWord C := by
  constructor <;> intro h <;> rw [h, add_assoc, parkerGolay_add_self, add_zero]

theorem octad_complementary_sum_switch (A B C : Octad) :
    octadWord A = octadWord B + octadWord C + golayOne ↔
      octadWord B = octadWord A + octadWord C + golayOne := by
  have h (b c : golay) : b + c + golayOne + c + golayOne = b := by
    rw [show b + c + golayOne + c + golayOne = b + (c + c) + (golayOne + golayOne) by abel,
      parkerGolay_add_self, parkerGolay_add_self, add_zero, add_zero]
  constructor <;> intro he <;> rw [he, h]

theorem octadBasisProduct_cubic_switch (A B C : Octad) :
    octadBasisProduct B C (Sum.inr A) = octadBasisProduct A C (Sum.inr B) := by
  classical
  rw [octadBasisProduct_octad_apply, octadBasisProduct_octad_apply]
  by_cases h : octadWord A = octadWord B + octadWord C
  · rw [if_pos h, if_pos ((octad_sum_switch A B C).mp h), octad_triangle_sign A B C h]
  · rw [if_neg h, if_neg (mt (octad_sum_switch A B C).mpr h)]
    by_cases h' : octadWord A = octadWord B + octadWord C + golayOne
    · rw [if_pos h', if_pos ((octad_complementary_sum_switch A B C).mp h'),
        octad_complementary_trio_sign A B C h']
    · rw [if_neg h', if_neg (mt (octad_complementary_sum_switch A B C).mpr h')]

end Atlas.Fischer

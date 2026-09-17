import Atlas.Fischer.ParkerLoopIdentities
import Atlas.Fischer.SignedOctads

namespace Atlas.Fischer
open Atlas.Codes

theorem octadWord_square_sign (O : Octad) :
    parkerGolayFactorSet (octadWord O) (octadWord O) = 0 := by
  rw [parkerGolayFactorSet_square]
  unfold golayQuarterWeight
  rw [octadWord_weight]
  rfl

theorem parker_one_square_sign : parkerGolayFactorSet golayOne golayOne = 0 := by
  have h := congrArg Prod.snd parkerOmega_square
  simpa [parkerOmega, parkerLoopMultiply, parkerMultiply] using h

theorem parker_one_commutator_sign (a : golay) :
    parkerGolayFactorSet golayOne a = parkerGolayFactorSet a golayOne := by
  have h := congrArg Prod.snd (parkerOmega_commutes (a, 0))
  simpa [parkerOmega, parkerLoopMultiply, parkerMultiply] using h

/-- The triangle sign identity follows from the actual ordered factor set. -/
theorem octad_triangle_sign (A B C : Octad)
    (h : octadWord A = octadWord B + octadWord C) :
    parkerGolayFactorSet (octadWord B) (octadWord C) =
      parkerGolayFactorSet (octadWord A) (octadWord C) := by
  rw [h, parkerGolayFactorSet_add_left, octadWord_square_sign, add_zero]

/-- The complementary-trio sign identity, including the Ω factor. -/
theorem octad_complementary_trio_sign (A B C : Octad)
    (h : octadWord A = octadWord B + octadWord C + golayOne) :
    parkerGolayFactorSet (octadWord B) (octadWord C) +
      parkerGolayFactorSet (octadWord B + octadWord C) golayOne =
    parkerGolayFactorSet (octadWord A) (octadWord C) +
      parkerGolayFactorSet (octadWord A + octadWord C) golayOne := by
  rw [h]
  simp only [parkerGolayFactorSet_add_left, octadWord_square_sign,
    parker_one_square_sign, parker_one_commutator_sign, add_zero]
  ring_nf
  simp only [show (3 : ParkerBit) = 1 from rfl, mul_one]

end Atlas.Fischer

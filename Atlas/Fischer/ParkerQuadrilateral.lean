import Atlas.Fischer.ParkerOmegaGauge

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerGolayFactorSet_quadrilateral (D F G : golay) :
    parkerGolayFactorSet F G + parkerGolayFactorSet (D + F) (D + G) +
      parkerGolayFactorSet D F + parkerGolayFactorSet D G =
        parkerGolayFactorSet D D + (overlap (D : BinaryWord) F / 2 : ℕ) +
          parkerTripleIntersection D F G := by
  simp only [parkerGolayFactorSet_add_left, parkerGolayFactorSet_add_right]
  simp only [Submodule.coe_add, parkerTripleIntersection_add_first]
  rw [parkerTripleIntersection_cycle (D : BinaryWord) D G,
    parkerTripleIntersection_repeat, parkerTripleIntersection_swap_first (F : BinaryWord) D G]
  have hc := parkerGolayFactorSet_commutator D F
  change parkerGolayFactorSet D F + parkerGolayFactorSet F D =
    (overlap (D : BinaryWord) F / 2 : ℕ) at hc
  have hz : (2 : ParkerBit) = 0 := by decide
  linear_combination (norm := ring_nf) hc
  all_goals simp only [hz, mul_zero, add_zero, zero_add, sub_zero]

theorem parkerChangedFactorSet_quadrilateral (s : golay → ParkerBit) (D F G : golay) :
    parkerChangedFactorSet s F G + parkerChangedFactorSet s (D + F) (D + G) +
      parkerChangedFactorSet s D F + parkerChangedFactorSet s D G =
        parkerGolayFactorSet D D + (overlap (D : BinaryWord) F / 2 : ℕ) +
          parkerTripleIntersection D F G := by
  have ht : D + F + (D + G) = F + G := by
    calc
      _ = (D + D) + (F + G) := by abel
      _ = _ := by rw [parkerGolay_add_self, zero_add]
  unfold parkerChangedFactorSet
  rw [ht]
  have hc := parkerGolayFactorSet_quadrilateral D F G
  have hz : (2 : ParkerBit) = 0 := by decide
  linear_combination (norm := ring_nf) hc
  all_goals simp only [hz, mul_zero, add_zero, zero_add, sub_zero]

theorem parkerChangedFactorSet_associator (s : golay → ParkerBit) (a b c : golay) :
    parkerChangedFactorSet s a b + parkerChangedFactorSet s (a + b) c +
      parkerChangedFactorSet s b c + parkerChangedFactorSet s a (b + c) =
        parkerTripleIntersection a b c := by
  unfold parkerChangedFactorSet
  rw [← add_assoc a b c]
  have hc := parkerGolayFactorSet_associator a b c
  have hz : (2 : ParkerBit) = 0 := by decide
  linear_combination (norm := ring_nf) hc
  all_goals simp only [hz, mul_zero, add_zero, zero_add, sub_zero]

end Atlas.Fischer

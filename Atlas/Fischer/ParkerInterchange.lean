import Atlas.Fischer.ParkerGolaySquareCommutator

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerTripleIntersection_swap_first (a b c : BinaryWord) :
    parkerTripleIntersection a b c = parkerTripleIntersection b a c := by
  unfold parkerTripleIntersection
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem parkerTripleIntersection_add_first (a b c d : BinaryWord) :
    parkerTripleIntersection (a + b) c d =
      parkerTripleIntersection a c d + parkerTripleIntersection b c d := by
  simp only [parkerTripleIntersection, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The six-sign interchange identity on arbitrary words of the retained Golay
code. It is derived from the actual factor set, not a signed-count table. -/
theorem parkerGolayFactorSet_interchange (D E G H : golay) :
    parkerGolayFactorSet D E + parkerGolayFactorSet G H +
      parkerGolayFactorSet D G + parkerGolayFactorSet E H +
      parkerGolayFactorSet (D + G) (E + H) + parkerGolayFactorSet (D + E) (G + H) =
        (overlap (E : BinaryWord) G / 2 : ℕ) +
          parkerTripleIntersection D E H + parkerTripleIntersection D G H := by
  simp only [parkerGolayFactorSet_add_left, parkerGolayFactorSet_add_right]
  simp only [Submodule.coe_add, parkerTripleIntersection_add_first]
  rw [parkerTripleIntersection_swap_first (G : BinaryWord) E H]
  have hc := parkerGolayFactorSet_commutator E G
  change parkerGolayFactorSet E G + parkerGolayFactorSet G E =
    (overlap (E : BinaryWord) G / 2 : ℕ) at hc
  have hz : (2 : ParkerBit) = 0 := by decide
  linear_combination (norm := ring_nf) hc
  all_goals simp only [hz, mul_zero, add_zero, zero_add]

/-- Changing the sign of each section lift adds this explicit coboundary. -/
noncomputable def parkerChangedFactorSet (s : golay → ParkerBit) (a b : golay) : ParkerBit :=
  parkerGolayFactorSet a b + s a + s b + s (a + b)

theorem parkerChangedFactorSet_interchange (s : golay → ParkerBit) (D E G H : golay) :
    parkerChangedFactorSet s D E + parkerChangedFactorSet s G H +
      parkerChangedFactorSet s D G + parkerChangedFactorSet s E H +
      parkerChangedFactorSet s (D + G) (E + H) +
        parkerChangedFactorSet s (D + E) (G + H) =
      (overlap (E : BinaryWord) G / 2 : ℕ) +
        parkerTripleIntersection D E H + parkerTripleIntersection D G H := by
  have ht : D + G + (E + H) = D + E + (G + H) := by abel
  unfold parkerChangedFactorSet
  rw [ht]
  have hc := parkerGolayFactorSet_interchange D E G H
  have hz : (2 : ParkerBit) = 0 := by decide
  linear_combination (norm := ring_nf) hc
  all_goals simp only [hz, mul_zero, add_zero, zero_add]

end Atlas.Fischer

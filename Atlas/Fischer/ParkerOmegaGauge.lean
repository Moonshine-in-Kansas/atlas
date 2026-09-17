import Atlas.Fischer.ParkerInterchange
import Atlas.Fischer.OctadCubicSigns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A symbolic change of section, using any retained coordinate, calibrates
the central all-one lift without changing the underlying Parker loop. -/
def parkerOmegaGauge (i : Omega) (w : golay) : ParkerBit :=
  w.val i * parkerGolayFactorSet w golayOne

def parkerOmegaFactorSet (i : Omega) (a b : golay) : ParkerBit :=
  parkerChangedFactorSet (parkerOmegaGauge i) a b

theorem parkerOmegaGauge_one (i : Omega) : parkerOmegaGauge i golayOne = 0 := by
  simp [parkerOmegaGauge, parker_one_square_sign]

theorem parkerOmegaGauge_add_one (i : Omega) (w : golay) :
    parkerOmegaGauge i (w + golayOne) =
      parkerOmegaGauge i w + parkerGolayFactorSet w golayOne := by
  simp only [parkerOmegaGauge, parkerGolayFactorSet_add_left, parker_one_square_sign, add_zero]
  change (w.val i + 1) * parkerGolayFactorSet w golayOne = _
  ring

theorem parkerOmegaFactorSet_one_right (i : Omega) (w : golay) :
    parkerOmegaFactorSet i w golayOne = 0 := by
  simp only [parkerOmegaFactorSet, parkerChangedFactorSet, parkerOmegaGauge_one,
    parkerOmegaGauge_add_one]
  ring_nf
  simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]

theorem parkerOmegaFactorSet_one_left (i : Omega) (w : golay) :
    parkerOmegaFactorSet i golayOne w = 0 := by
  have he : parkerOmegaFactorSet i golayOne w = parkerOmegaFactorSet i w golayOne := by
    unfold parkerOmegaFactorSet parkerChangedFactorSet
    rw [parker_one_commutator_sign, add_comm golayOne w]
    abel
  rw [he, parkerOmegaFactorSet_one_right]

theorem parkerOmegaFactorSet_shift_left (i : Omega) (a b : golay) :
    parkerOmegaFactorSet i (a + golayOne) b = parkerOmegaFactorSet i a b := by
  unfold parkerOmegaFactorSet parkerChangedFactorSet
  have ht : a + golayOne + b = a + b + golayOne := by abel
  rw [ht]
  simp only [parkerGolayFactorSet_add_left, parker_one_commutator_sign,
    parkerOmegaGauge_add_one]
  ring_nf
  simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]

theorem parkerOmegaFactorSet_shift_right (i : Omega) (a b : golay) :
    parkerOmegaFactorSet i a (b + golayOne) = parkerOmegaFactorSet i a b := by
  unfold parkerOmegaFactorSet parkerChangedFactorSet
  rw [← add_assoc a b golayOne]
  simp only [parkerGolayFactorSet_add_right, parkerOmegaGauge_add_one,
    parkerGolayFactorSet_add_left]
  have ht : parkerTripleIntersection (a : BinaryWord) b golayOne = 0 := by
    rw [parkerTripleIntersection_cycle, parkerTripleIntersection_one]
  rw [ht]
  ring_nf
  simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]

end Atlas.Fischer

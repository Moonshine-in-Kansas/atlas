import Atlas.Fischer.ParkerGolayFactorSet
import Atlas.Fischer.ParkerBinaryDetermination

namespace Atlas.Fischer

open Atlas.Codes
open scoped BigOperators

theorem parkerGolayFactorSet_add_left (a b c : golay) :
    parkerGolayFactorSet (a + b) c =
      parkerGolayFactorSet a c + parkerGolayFactorSet b c := by
  simp only [parkerGolayFactorSet, map_add, Finsupp.coe_add, parkerOrderedFactorSet,
    parkerOrderedTheta_add_left, parkerOrderedBeta_add_left]
  ring

theorem parkerGolayFactorSet_add_right (a b c : golay) :
    parkerGolayFactorSet a (b + c) = parkerGolayFactorSet a b +
      parkerGolayFactorSet a c + parkerTripleIntersection a b c := by
  have h := parkerGolayFactorSet_associator a b c
  rw [parkerGolayFactorSet_add_left] at h
  have h2 : ∀ x : ParkerBit, x + x = 0 := by decide
  have h' := congrArg (fun x => x + parkerGolayFactorSet a b +
    parkerGolayFactorSet a c) h
  convert h' using 1 <;> ring_nf <;>
    simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, zero_add, add_zero]

theorem parkerGolayFactorSet_basis (i j : Fin 12) :
    parkerGolayFactorSet (golayBasis i) (golayBasis j) =
      parkerGolayBilinearCoefficients i j := by
  classical
  simp [parkerGolayFactorSet, parkerOrderedFactorSet, parkerOrderedTheta,
    parkerOrderedBeta, Module.Basis.repr_self, Finsupp.single_apply, ite_mul, mul_ite]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro z _
  by_cases hy : j = y <;> by_cases hz : j = z <;> simp_all

end Atlas.Fischer

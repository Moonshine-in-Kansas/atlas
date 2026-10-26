import Atlas.Lattices.ConwayWales.CyclicFactors
import Atlas.LinearAlgebra.DoubledCoordinates
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.SetTheory.Cardinal.Finite

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open Polynomial

theorem cyclicFactorZero_monic : cyclicFactorZero.Monic := by
  unfold cyclicFactorZero
  monicity <;> norm_num

theorem cyclicFactorPlus_monic : cyclicFactorPlus.Monic := by
  unfold cyclicFactorPlus
  monicity <;> norm_num

theorem cyclicFactorMinus_monic : cyclicFactorMinus.Monic := by
  unfold cyclicFactorMinus
  monicity <;> norm_num

theorem cyclicFactorZero_degree : cyclicFactorZero.natDegree = 1 := by
  unfold cyclicFactorZero
  compute_degree <;> norm_num <;> decide

theorem cyclicFactorPlus_degree : cyclicFactorPlus.natDegree = 3 := by
  unfold cyclicFactorPlus
  compute_degree <;> norm_num <;> decide

theorem cyclicFactorMinus_degree : cyclicFactorMinus.natDegree = 3 := by
  unfold cyclicFactorMinus
  compute_degree <;> norm_num <;> decide

/-- Cardinality from the monic power basis, over a ring rather than a field. -/
theorem cyclicComponent_card (f : Polynomial (ZMod 4)) (hf : f.Monic) :
    Nat.card (CyclicComponent f) = 4 ^ f.natDegree := by
  change Nat.card (AdjoinRoot f) = _
  rw [Nat.card_congr (AdjoinRoot.powerBasisAux' hf).equivFun.toEquiv]
  simp

theorem cyclicComponentZero_card : Nat.card (CyclicComponent cyclicFactorZero) = 4 := by
  rw [cyclicComponent_card _ cyclicFactorZero_monic, cyclicFactorZero_degree] <;> norm_num

theorem cyclicComponentPlus_card : Nat.card (CyclicComponent cyclicFactorPlus) = 64 := by
  rw [cyclicComponent_card _ cyclicFactorPlus_monic, cyclicFactorPlus_degree] <;> norm_num

theorem cyclicComponentMinus_card : Nat.card (CyclicComponent cyclicFactorMinus) = 64 := by
  rw [cyclicComponent_card _ cyclicFactorMinus_monic, cyclicFactorMinus_degree] <;> norm_num

/-- The cardinality of the actual doubled ideal, obtained from the monic basis. -/
theorem cyclicComponent_doubled_card (f : Polynomial (ZMod 4)) (hf : f.Monic) :
    Nat.card (Atlas.LinearAlgebra.Doubled (CyclicComponent f)) =
      2 ^ f.natDegree := by
  have h := Atlas.LinearAlgebra.doubled_card (AdjoinRoot.powerBasisAux' hf).equivFun
  simp only [Atlas.LinearAlgebra.Doubled, two_nsmul, Fintype.card_fin] at h ⊢
  convert h using 1
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.refl _) (fun x => ?_)
  rfl

theorem cyclicComponentPlus_doubled_card :
    Nat.card (Atlas.LinearAlgebra.Doubled (CyclicComponent cyclicFactorPlus)) = 8 := by
  rw [cyclicComponent_doubled_card _ cyclicFactorPlus_monic, cyclicFactorPlus_degree]
  norm_num

theorem cyclicComponentMinus_doubled_card :
    Nat.card (Atlas.LinearAlgebra.Doubled (CyclicComponent cyclicFactorMinus)) = 8 := by
  rw [cyclicComponent_doubled_card _ cyclicFactorMinus_monic, cyclicFactorMinus_degree]
  norm_num

end Atlas.ConwayWales


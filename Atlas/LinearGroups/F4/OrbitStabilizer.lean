import Atlas.LinearGroups.F4.PointTransitivity
import Atlas.LinearGroups.F4.PointCountSum
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Actual orbit–stabilizer decomposition. The remaining factor is the actual
full point stabilizer; its numerical order is not asserted here. -/
namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

theorem groupCard_eq_pointCount_mul_stabilizer : Nat.card (Model F)=
    Nat.card (WhiteZeroPoints F)*Nat.card (parabolicPointStabilizer (F:=F)) := by
  rw [←Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Model F)
    (parabolicPoint (F:=F))),Nat.card_prod]
  congr 1
  rw [MulAction.orbit_eq_univ]
  exact Nat.card_congr (Equiv.Set.univ (WhiteZeroPoints F))

end Atlas.F4

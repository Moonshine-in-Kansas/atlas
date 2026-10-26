import Atlas.LinearGroups.F4.WhiteZeroPoints
import Atlas.Algebra.Albert.WhiteZeroCount

namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

theorem card_whiteZeroPoints : Nat.card (WhiteZeroPoints F) =
    ((Nat.card F^12-1)*(Nat.card F^4+1))/(Nat.card F-1) := by
  change Nat.card (Atlas.LinearAlgebra.ConePoints (F:=F)
    (fun x : Atlas.Albert.Carrier F => Atlas.Albert.trace x=0 ∧ Atlas.Albert.adjoint x=0)) = _
  rw [Atlas.LinearAlgebra.card_conePoints _ (whiteZero_smul_iff F),
    Nat.card_congr (nonzeroConeEquivWhiteZeroVectors F),Atlas.Albert.card_whiteZeroVectors]

end Atlas.F4

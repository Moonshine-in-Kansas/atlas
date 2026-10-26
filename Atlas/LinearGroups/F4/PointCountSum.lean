import Atlas.LinearGroups.F4.PointCount
import Mathlib.Algebra.Ring.GeomSum

namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

theorem card_whiteZeroPoints_sum : Nat.card (WhiteZeroPoints F) =
    (Nat.card F^4+1) * ∑ i ∈ Finset.range 12, Nat.card F^i := by
  rw [card_whiteZeroPoints,mul_comm (Nat.card F^12-1),
    Nat.mul_div_assoc _ (Nat.sub_one_dvd_pow_sub_one (Nat.card F) 12),
    ←Nat.geomSum_eq (Finite.one_lt_card (α:=F)) 12]

end Atlas.F4

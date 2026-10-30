import Atlas.LinearGroups.ReeG2.Order
import Atlas.LinearGroups.ReeG2.FaithfulAction

/-! The excluded simplicity endpoint uses the same generated matrix model.
These statements specialize existing all-parameter structure; no replacement
by a semilinear group, derived-subgroup identification or simplicity is assumed. -/
noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem smallParameter_card_condition (hF : Nat.card F = 3) :
    Nat.card F = 3 ^ (2 * 0 + 1) := by simpa using hF

theorem smallParameter_order (hF : Nat.card F = 3) :
    Nat.card (Model F 0) = 1512 := by
  simpa [hF] using order 0 (smallParameter_card_condition hF)

theorem smallParameter_point_count (hF : Nat.card F = 3) :
    Nat.card (pointSet (F := F) 0) = 28 := by
  simpa [hF] using card_pointSet (F := F) 0

theorem smallParameter_borel_order (hF : Nat.card F = 3) :
    Nat.card (borel 0 (smallParameter_card_condition hF)) = 54 := by
  simpa [hF] using card_borel (F := F) 0 (smallParameter_card_condition hF)

theorem smallParameter_faithful (hF : Nat.card F = 3) :
    letI := pointAction 0 (smallParameter_card_condition hF)
    FaithfulSMul (Model F 0) (pointSet (F := F) 0) :=
  pointAction_faithful 0 (smallParameter_card_condition hF)

theorem smallParameter_primitive (hF : Nat.card F = 3) :
    letI := pointAction 0 (smallParameter_card_condition hF)
    MulAction.IsPreprimitive (Model F 0) (pointSet (F := F) 0) :=
  pointAction_preprimitive 0 (smallParameter_card_condition hF)

end Atlas.ReeG2

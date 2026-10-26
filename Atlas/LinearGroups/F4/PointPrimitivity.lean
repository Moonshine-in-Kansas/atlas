import Atlas.LinearGroups.F4.PointPrimitivityCriterion
import Atlas.LinearGroups.F4.NearPointEscape
import Atlas.LinearGroups.F4.NonNearPointEscape

/-! Primitivity of the actual white-point action, from explicit stabilizer
moves in the near nine-space and short-root displacement outside it. -/
namespace Atlas.F4
variable {F : Type*} [Field F]

/-- The intrinsic Albert action is primitive, uniformly in characteristic. -/
theorem whiteZeroPoints_primitive :
    MulAction.IsPreprimitive (Model F) (WhiteZeroPoints F) := by
  classical
  apply whiteZeroPoints_primitive_of_base_escape
  intro x hne _
  by_cases hx : x.val.rep ∈ parabolicImageZero (F:=F)
  · exact nearPoint_stabilizer_chain_escape x hx hne
  · exact nonnear_point_stabilizer_chain_escape x hx

end Atlas.F4

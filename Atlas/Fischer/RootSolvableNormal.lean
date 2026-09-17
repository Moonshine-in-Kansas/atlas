import Atlas.Algebra.SolvableNormalPSubgroup
import Atlas.Fischer.RootNormalPSubgroups

/-! The actual generated ray group has no nontrivial solvable normal subgroup. -/
namespace Atlas.Fischer

theorem rootGeneratedRay_solvable_normal_eq_bot
    (N : Subgroup rootGeneratedRayGroup) [N.Normal] [Group.IsSolvable N] : N = ⊥ := by
  exact Atlas.Algebra.solvable_normal_eq_bot_of_no_normal_pgroup
    rootGeneratedRay_normal_pgroup_eq_bot N

end Atlas.Fischer

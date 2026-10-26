import Atlas.LinearGroups.F4.Generation
import Atlas.LinearGroups.F4.RadicalNormalPropagation

/-! Perfectness from the actual all-characteristic A₂ root commutators, and
normal generation by the explicit solvable local subgroup. No numerical F₄
order is used. -/
namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

theorem isPerfect : Group.IsPerfect (Model F) := by
  constructor
  apply top_unique
  rw [←generated_eq_top]
  exact rootGenerated_le_commutator

theorem normal_eq_top_of_contains_radical (N : Subgroup (Model F)) [N.Normal]
    (hR : radicalSubgroup (F:=F) ≤ N) : N=⊤ := by
  apply top_unique
  rw [←generated_eq_top]
  exact rootGenerated_le_of_normal_contains_radical N hR

end Atlas.F4

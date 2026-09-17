import Atlas.LinearGroups.ReeG2.Perfect
import Atlas.LinearGroups.ReeG2.FaithfulAction
import Atlas.LinearGroups.ReeG2.Order
import Atlas.LinearGroups.ReeG2.BorelSolvable
import Atlas.LinearGroups.ReeG2.Noncommutative
import Atlas.GroupTheory.SolvableStabilizerSimplicity

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Simplicity of the actual seven-dimensional Ree matrix group for every q≥27. -/
theorem simple (m : ℕ) (hp : Parameters F m) : IsSimpleGroup (Model F m) := by
  letI := pointAction m hp.cardinality
  letI : Nontrivial (Model F m) := by
    obtain ⟨g,h,hne⟩ := model_noncommutative m hp.cardinality
    exact ⟨⟨g*h,h*g,hne⟩⟩
  letI := perfect m hp
  letI := pointAction_preprimitive m hp.cardinality
  letI := pointAction_faithful m hp.cardinality
  letI := borel_solvable m hp.cardinality
  letI : Group.IsSolvable (MulAction.stabilizer (Model F m) (infinity (F := F) m)) := by
    rw [infinityStabilizer_eq_borel m hp.cardinality]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (borel_le_generated m hp.cardinality)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (borel_le_generated m hp.cardinality)).injective
  exact Atlas.GroupTheory.simple_of_perfect_quasiprimitive_solvable_stabilizer
    (infinity (F := F) m)

end Atlas.ReeG2

import Atlas.LinearGroups.Triality.ParabolicAction
import Atlas.LinearGroups.Triality.RadicalGeneration
import Atlas.LinearGroups.Triality.Perfect
import Atlas.GroupTheory.IwasawaSolvableRadical

/-! Uniform simplicity of the actual triality matrix group, including q=2. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def parabolicRadical : Subgroup (Group F K) :=
  (longRadical F K hdeg).subgroupOf (generated F K)

theorem parabolicRadical_le : parabolicRadical F K hdeg ≤ parabolic F K hdeg :=
  fun _ hx => longRadical_le_parabolic F K hdeg hx

theorem parabolicRadical_normal :
    ((parabolicRadical F K hdeg).subgroupOf (parabolic F K hdeg)).Normal := by
  constructor
  intro x hx g
  exact (Subgroup.mem_normalizer_iff.mp
    (longParabolic_normalizes_radical F K hdeg g.property) x.val.val).mp hx

theorem parabolicRadical_solvable : _root_.Group.IsSolvable (parabolicRadical F K hdeg) := by
  letI := longRadical_solvable F K hdeg
  have hle : longRadical F K hdeg ≤ generated F K :=
    le_trans (longRadical_le_parabolic F K hdeg) (longParabolic_le_generated F K hdeg)
  exact _root_.Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).injective

include hdeg in
/-- No small-field exception: the same matrix group is simple for every cubic
extension of finite fields, including base cardinalities two and three. -/
theorem simple : IsSimpleGroup (Group F K) := by
  letI := perfect F K hdeg
  letI := parabolicRadical_solvable F K hdeg
  apply Atlas.GroupTheory.iwasawa_solvable_radical_simple
    ((1 : Group F K) : ParabolicPoints F K hdeg) (parabolicRadical F K hdeg)
  · rw [MulAction.stabilizer_quotient]
    exact parabolicRadical_le F K hdeg
  · rw [MulAction.stabilizer_quotient]
    exact parabolicRadical_normal F K hdeg
  · exact longRadical_normalClosure F K hdeg

end Atlas.Triality

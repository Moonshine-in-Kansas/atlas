import Atlas.LinearGroups.Triality.RadicalNormalizers

/-! The actual relative parabolic candidates and their normal solvable radicals.
Properness, maximality and the action kernel are not assumed here. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def shortParabolic : Subgroup (O_DPlus 4 K) :=
  borel F K hdeg ⊔ Subgroup.closure {shortWeyl F K}

theorem shortParabolic_le_generated : shortParabolic F K hdeg ≤ generated F K := by
  apply sup_le (borel_le_generated F K hdeg)
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_singleton_iff.mp hg with rfl
  exact shortWeyl_mem F K

theorem shortRadical_le_parabolic : shortRadical F K hdeg ≤ shortParabolic F K hdeg :=
  le_trans (le_trans (shortRadical_le_unipotent F K hdeg) (unipotent_le_borel F K hdeg)) le_sup_left

theorem shortParabolic_normalizes_radical :
    shortParabolic F K hdeg ≤ Subgroup.normalizer (shortRadical F K hdeg : Set (O_DPlus 4 K)) := by
  apply sup_le
  · rw [borel_eq_sup F K hdeg]
    exact sup_le (unipotent_normalizes_shortRadical F K hdeg) (torus_normalizes_shortRadical F K hdeg)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact shortWeyl_normalizes_shortRadical F K hdeg

theorem shortRadical_normal_in_parabolic :
    ((shortRadical F K hdeg).subgroupOf (shortParabolic F K hdeg)).Normal := by
  constructor
  intro x hx g
  exact (Subgroup.mem_normalizer_iff.mp (shortParabolic_normalizes_radical F K hdeg g.property) x.val).mp hx

theorem shortRadical_solvable : _root_.Group.IsSolvable (shortRadical F K hdeg) := by
  letI := unipotent_solvable F K hdeg
  exact _root_.Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (shortRadical_le_unipotent F K hdeg))

def longParabolic : Subgroup (O_DPlus 4 K) :=
  borel F K hdeg ⊔ Subgroup.closure {longWeyl F K}

theorem longParabolic_le_generated : longParabolic F K hdeg ≤ generated F K := by
  apply sup_le (borel_le_generated F K hdeg)
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_singleton_iff.mp hg with rfl
  exact longWeyl_mem F K

theorem longRadical_le_parabolic : longRadical F K hdeg ≤ longParabolic F K hdeg :=
  le_trans (le_trans (longRadical_le_unipotent F K hdeg) (unipotent_le_borel F K hdeg)) le_sup_left

theorem longParabolic_normalizes_radical :
    longParabolic F K hdeg ≤ Subgroup.normalizer (longRadical F K hdeg : Set (O_DPlus 4 K)) := by
  apply sup_le
  · rw [borel_eq_sup F K hdeg]
    exact sup_le (unipotent_normalizes_longRadical F K hdeg) (torus_normalizes_longRadical F K hdeg)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact longWeyl_normalizes_longRadical F K hdeg

theorem longRadical_normal_in_parabolic :
    ((longRadical F K hdeg).subgroupOf (longParabolic F K hdeg)).Normal := by
  constructor
  intro x hx g
  exact (Subgroup.mem_normalizer_iff.mp (longParabolic_normalizes_radical F K hdeg g.property) x.val).mp hx

theorem longRadical_solvable : _root_.Group.IsSolvable (longRadical F K hdeg) := by
  letI := unipotent_solvable F K hdeg
  exact _root_.Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (longRadical_le_unipotent F K hdeg))

end Atlas.Triality

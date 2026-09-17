import Atlas.Conway.McLSimplicity
import Atlas.GroupTheory.NonabelianSimplePerfect
import Mathlib.GroupTheory.Abelianization.Defs

noncomputable section
namespace Atlas.Sporadic.McLaughlin
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped IsMulCommutative

theorem isSimpleGroup : IsSimpleGroup Model := mcl_simple

theorem perfect : Group.IsPerfect Model := by
  letI := isSimpleGroup
  exact Atlas.GroupTheory.nonabelian_simple_perfect Model exists_mul_ne_mul

theorem pair_commutator_eq_kernel : commutator PairStabilizer = endpointPermutation.ker := by
  letI : IsMulCommutative (Equiv.Perm Endpoints) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr (by rw [mcl_endpoints_card])
  apply le_antisymm (Abelianization.commutator_subset_ker endpointPermutation)
  letI := perfect
  haveI : Group.IsPerfect toPairStabilizer.range := Group.IsPerfect.range toPairStabilizer
  have hr : toPairStabilizer.range ≤ commutator PairStabilizer := by
    rw [← toPairStabilizer.range.commutator_eq_self]
    exact Subgroup.commutator_mono le_top le_top
  rw [toPairStabilizer_range] at hr
  exact hr

theorem pair_commutator_eq_model_image : commutator PairStabilizer = toPairStabilizer.range := by
  rw [pair_commutator_eq_kernel,toPairStabilizer_range]

end Atlas.Sporadic.McLaughlin

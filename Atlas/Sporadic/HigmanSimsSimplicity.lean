import Atlas.Sporadic.HigmanSims
import Atlas.Conway.HSSimplicity
import Atlas.GroupTheory.NonabelianSimplePerfect

noncomputable section
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway MulAction

theorem primitive : IsPreprimitive Model Points := hs_graph_primitive

theorem regular_normal_impossible (N : Subgroup Model) [N.Normal]
    [IsPretransitive N Points]
    (h : ∀ n : N, n • basePoint = basePoint → n = 1) : False :=
  hs_regular_normal_impossible N h

theorem isSimpleGroup : IsSimpleGroup Model := hs_simple

theorem perfect : Group.IsPerfect Model := by
  letI := isSimpleGroup
  exact Atlas.GroupTheory.nonabelian_simple_perfect Model exists_mul_ne_mul

end Atlas.Sporadic.HigmanSims

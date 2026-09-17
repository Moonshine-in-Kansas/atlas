import Atlas.Lattices.IcosianComparisonGeneratorsData

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Matrix

theorem icosianComparisonSourceGenerator_mem (j : Fin 36) :
    icosianComparisonSourceGenerator j ∈ icosianLeechModule := by
  rw [icosianLeechModule_mem,icosianP_mem,icosianP_mem,icosianPZero_mem]
  simp only [icosianComparisonSourceGenerator,map_sub,map_add,icosianModuloTwo_synthesis,
    Matrix.sub_apply,Matrix.add_apply]
  revert j
  decide +kernel

end Atlas.Lattices

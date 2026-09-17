import Atlas.Conway.IcosianPrimitivity

noncomputable section
namespace Atlas.Conway

/-- Nonabelian simplicity of the actual sign quotient of the full
right-quaternion-linear Hermitian stabilizer of the icosian Leech lattice. -/
theorem icosianProjective_simple : IsSimpleGroup IcosianProjectiveModel := by
  letI := icosianProjective_rootPoint_primitive
  exact icosianProjective_simple_of_primitive

end Atlas.Conway

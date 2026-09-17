import Atlas.Lattices.EisensteinRank

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

instance eisensteinLeech_scalar_finite : Module.Finite Eisenstein eisensteinLeechModule :=
  Module.Finite.of_restrictScalars_finite ℤ Eisenstein eisensteinLeechModule

/-- Multiplication by nine gives an actual integral scalar-linear injection from
the ambient free rank-twelve module into the congruence lattice. -/
def eisensteinNineScalarIntoLattice : EisensteinCoordinates →ₗ[Eisenstein] eisensteinLeechModule where
  toFun z := ⟨(9 : Eisenstein) • z,eisensteinLeechModule_contains_nine z⟩
  map_add' z w := by apply Subtype.ext; exact smul_add _ _ _
  map_smul' r z := by apply Subtype.ext; exact smul_comm _ _ _

theorem eisensteinNineScalarIntoLattice_injective :
    Function.Injective eisensteinNineScalarIntoLattice :=
  eisensteinNineIntoLattice_injective

/-- The actual Eisenstein module has rank twelve. This uses two integral
injections and finite generation, without assuming a basis or a field comparison. -/
theorem eisensteinLeech_scalar_rank : Module.finrank Eisenstein eisensteinLeechModule=12 := by
  have h₁ := LinearMap.finrank_le_finrank_of_injective eisensteinLeechModule.subtype_injective
  have h₂ := LinearMap.finrank_le_finrank_of_injective eisensteinNineScalarIntoLattice_injective
  have h : Module.finrank Eisenstein EisensteinCoordinates=12 := by
    simp [EisensteinCoordinates,Module.finrank_pi_fintype]
  rw [h] at h₁ h₂
  omega

end Atlas.Lattices

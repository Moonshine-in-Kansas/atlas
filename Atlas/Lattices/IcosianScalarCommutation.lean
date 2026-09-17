import Atlas.Lattices.IcosianRightLinearity
import Atlas.Lattices.IcosianScalarAction

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Quaternion

def icosianScalarI : icosianNormOneGroup :=
  icosianNormOneGroupOf icosianI icosianI_mem (by
    norm_num [icosianNorm,Quaternion.normSq_def',icosianI])

def icosianScalarGenerator : icosianNormOneGroup :=
  icosianNormOneGroupOf icosianGenerator icosianGenerator_mem (by
    ext <;> norm_num [icosianNorm,Quaternion.normSq_def',icosianGenerator,pow_two] <;> rfl)

theorem icosianScalarI_inverse_action (x : IcosianRationalCoordinates) :
    icosianScalarRepresentation (icosianScalarI⁻¹) x=icosianRightMul x icosianI := by
  funext j
  simp [icosianScalarRepresentation,icosianRightUnitEquiv,icosianScalarI,
    icosianNormOneGroupOf,icosianRightMul]

theorem icosianScalarGenerator_inverse_action (x : IcosianRationalCoordinates) :
    icosianScalarRepresentation (icosianScalarGenerator⁻¹) x=
      icosianRightMul x icosianGenerator := by
  funext j
  simp [icosianScalarRepresentation,icosianRightUnitEquiv,icosianScalarGenerator,
    icosianNormOneGroupOf,icosianRightMul]

/-- The full right-D linearity condition is exactly centralization of the actual
integral norm-one scalar group; its two order generators already suffice. -/
theorem icosian_right_linear_iff_scalar_commutation
    (f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates) :
    (∀ a x,f (icosianRightMul x a)=icosianRightMul (f x) a) ↔
      ∀ u, f*icosianScalarRepresentation u=icosianScalarRepresentation u*f := by
  constructor
  · intro h u
    apply LinearEquiv.ext
    intro x
    exact h _ x
  · intro h
    apply icosian_right_linear_of_generators f.toLinearMap
    · intro x
      change f (icosianRightMul x icosianI)=icosianRightMul (f x) icosianI
      have he := LinearEquiv.congr_fun (h (icosianScalarI⁻¹)) x
      simpa only [LinearEquiv.mul_apply,icosianScalarI_inverse_action] using he
    · intro x
      change f (icosianRightMul x icosianGenerator)=icosianRightMul (f x) icosianGenerator
      have he := LinearEquiv.congr_fun (h (icosianScalarGenerator⁻¹)) x
      simpa only [LinearEquiv.mul_apply,icosianScalarGenerator_inverse_action] using he

end Atlas.Lattices

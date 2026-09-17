import Atlas.LinearGroups.Orthogonal.B2ExteriorKernel
import Atlas.LinearGroups.Orthogonal.B2ExteriorScalar
import Atlas.LinearGroups.Orthogonal.B2ExteriorImage

noncomputable section
namespace Atlas.Orthogonal.B2Exterior
variable {F : Type*} [Field F]

/-- The exact scalar-center kernel, proved through the actual exterior-square matrices. -/
theorem toOrthogonal_eq_one_iff_center (h2 : (2 : F) ≠ 0)
    (g : Atlas.Symplectic.Sp 2 F) :
    toOrthogonal g = 1 ↔ g ∈ Subgroup.center (Atlas.Symplectic.Sp 2 F) := by
  constructor
  · intro hg
    obtain ⟨c, _, hc⟩ := scalar_of_toOrthogonal_eq_one h2 g hg
    exact Atlas.Symplectic.scalar_is_central g c (symplecticMatrix_scalar_action g c hc)
  · exact toOrthogonal_eq_one_of_center g

/-- Equality of actual subgroups, not merely their orders. -/
theorem toOrthogonal_kernel (h2 : (2 : F) ≠ 0) :
    (toOrthogonal (F := F)).ker = Subgroup.center (Atlas.Symplectic.Sp 2 F) := by
  ext g
  exact toOrthogonal_eq_one_iff_center h2 g

/-- The same exact kernel for the image in the intrinsic elementary orthogonal group. -/
theorem toElementary_kernel [Finite F] (h2 : (2 : F) ≠ 0) :
    (toElementary (F := F) h2).ker = Subgroup.center (Atlas.Symplectic.Sp 2 F) := by
  ext g
  change toElementary h2 g = 1 ↔ g ∈ Subgroup.center (Atlas.Symplectic.Sp 2 F)
  rw [← toOrthogonal_eq_one_iff_center h2 g]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Atlas.Orthogonal.B2Exterior

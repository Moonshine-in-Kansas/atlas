import Atlas.Lattices.IcosianIntegralScalarAction
import Atlas.Conway.IcosianScalarIsometries

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- The previously constructed scalar-unit isometry is exactly the integral
endomorphism belonging to its inverse right scalar. -/
theorem icosianLeechRightScalars_unit (u : icosianNormOneGroup) (x : leech) :
    icosianLeechRightScalars (MulOpposite.op (icosianNormOneToOrder (u⁻¹))) x=
      (icosianScalarsToCo0 u).val x := by
  obtain ⟨z,rfl⟩ := icosianLeechEquiv.surjective x
  apply Subtype.ext
  apply rationalEmbedding_injective
  rw [icosianLeechRightScalars_rational]
  have h := congrArg (fun f : rationalLatticeIsometries =>
    f.val (icosianComparison (icosianCoordinateEmbedding z.val)))
      (icosianScalarsToCo0_extension u)
  change rationalExtension (icosianScalarsToCo0 u).val
      (icosianComparison (icosianCoordinateEmbedding z.val))=
    icosianRationalScalar u (icosianComparison (icosianCoordinateEmbedding z.val)) at h
  rw [← icosianLeechEquiv_agrees,rationalExtension_agrees] at h
  rw [h]
  rw [icosianLeechEquiv_agrees]
  change icosianComparison (fun i => (z.val i).val*(icosianNormOneToOrder (u⁻¹)).val)=
    icosianComparison (icosianScalarRepresentation u
      (icosianComparison.symm (icosianComparison (icosianCoordinateEmbedding z.val))))
  rw [icosianComparison.symm_apply_apply]
  rfl

end Atlas.Conway

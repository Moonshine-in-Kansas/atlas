import Atlas.Fischer.FullSemilinearGeneration

noncomputable section
namespace Atlas.Fischer
attribute [local instance] scalarAlgebraRepresentation_range_normal

/-- The full semilinear automorphism action, with its proved actual generated
ray group as codomain. -/
def fullSemilinearRayProjection : SemilinearAlgebraAutomorphism →* rootGeneratedRayGroup :=
  semilinearDisplayedRayAction.codRestrict rootGeneratedRayGroup (fun e => by
    rw [← semilinearDisplayedRayAction_range]
    exact ⟨e,rfl⟩)

theorem fullSemilinearRayProjection_surjective : Function.Surjective fullSemilinearRayProjection := by
  intro g
  obtain ⟨e,he⟩ := rootGeneratedRayGroup_lift g
  exact ⟨e.val,Subtype.ext he⟩

theorem fullSemilinearRayProjection_kernel :
    fullSemilinearRayProjection.ker=scalarAlgebraRepresentation.range := by
  rw [← semilinearRayKernel_eq_scalar_range]
  ext e
  change (fullSemilinearRayProjection e=1) ↔ semilinearDisplayedRayAction e=1
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

/-- The actual full semilinear quotient by cubic scalars is the root-generated
ray group. The scalar subgroup is normal here, not asserted central. -/
def fullSemilinearScalarQuotientEquiv :
    SemilinearAlgebraAutomorphism ⧸ scalarAlgebraRepresentation.range ≃* rootGeneratedRayGroup :=
  (QuotientGroup.quotientMulEquivOfEq fullSemilinearRayProjection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fullSemilinearRayProjection
      fullSemilinearRayProjection_surjective)

end Atlas.Fischer

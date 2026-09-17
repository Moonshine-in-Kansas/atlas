import Atlas.Fischer.GeneratedCubicScalars
import Atlas.Fischer.GeneratedDerivedSubgroups
import Atlas.Fischer.RayKernelScalarSubgroup

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The retained scalar maps inside the actual generated algebra group. -/
def generatedScalarHom : Mu3 →* rootGeneratedAlgebraGroup :=
  scalarAlgebraRepresentation.codRestrict rootGeneratedAlgebraGroup
    scalarAlgebraRepresentation_mem_generated

/-- Cubic scalars lie in the actual positive subgroup. -/
def positiveScalarHom : Mu3 →* rootGeneratedAlgebraParity.ker :=
  generatedScalarHom.codRestrict rootGeneratedAlgebraParity.ker (fun a => by
    change Multiplicative.ofAdd (semilinearAlgebraParity (scalarAlgebraRepresentation a))=1
    rw [scalarAlgebraRepresentation_parity]
    rfl)

theorem positiveScalarHom_injective : Function.Injective positiveScalarHom := by
  intro a b h
  apply scalarAlgebraRepresentation_injective
  exact congrArg (fun e : rootGeneratedAlgebraParity.ker => e.val.val) h

/-- Exactness identifies the literal positive ray projection kernel with the
retained scalar subgroup, rather than an abstract group of the same order. -/
theorem rootGeneratedPositiveProjection_kernel :
    rootGeneratedPositiveProjection.ker=positiveScalarHom.range := by
  ext g
  constructor
  · intro hg
    have hker : g.val.val ∈ semilinearRayKernel := by
      change semilinearDisplayedRayAction g.val.val=1
      exact congrArg (fun e : rootGeneratedRayParity.ker => e.val.val) hg
    rw [semilinearRayKernel_eq_scalar_range] at hker
    obtain ⟨a,ha⟩ := hker
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ha
  · rintro ⟨a,rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    have hker : scalarAlgebraRepresentation a ∈ semilinearRayKernel := by
      rw [semilinearRayKernel_eq_scalar_range]
      exact ⟨a,rfl⟩
    exact hker

/-- Centrality is asserted only in the positive, linear algebra subgroup. -/
theorem positiveScalarHom_range_central :
    positiveScalarHom.range ≤ Subgroup.center rootGeneratedAlgebraParity.ker := by
  rintro z ⟨a,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hp : semilinearAlgebraParity g.val.val=0 :=
    congrArg Multiplicative.toAdd g.property
  change g.val.val.val ((a.val.val : Scalar) • x)=
    (a.val.val : Scalar) • g.val.val.val x
  rw [semilinearAlgebraParity_spec,hp,scalarParityAut_zero]

theorem rootGeneratedPositiveProjection_kernel_central :
    rootGeneratedPositiveProjection.ker ≤ Subgroup.center rootGeneratedAlgebraParity.ker := by
  rw [rootGeneratedPositiveProjection_kernel]
  exact positiveScalarHom_range_central

theorem rootGeneratedPositiveProjection_kernel_card :
    Nat.card rootGeneratedPositiveProjection.ker=3 := by
  rw [rootGeneratedPositiveProjection_kernel,
    ← Nat.card_congr (MonoidHom.ofInjective positiveScalarHom_injective).toEquiv,mu3_card]

instance positiveScalarRangeNormal : positiveScalarHom.range.Normal := by
  rw [← rootGeneratedPositiveProjection_kernel]
  infer_instance

/-- The quotient by the retained cubic scalars is the actual positive ray group. -/
def positiveScalarQuotientEquiv :
    rootGeneratedAlgebraParity.ker ⧸ positiveScalarHom.range ≃* rootGeneratedRayParity.ker := by
  exact (QuotientGroup.quotientMulEquivOfEq rootGeneratedPositiveProjection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective rootGeneratedPositiveProjection
      rootGeneratedPositiveProjection_surjective)

end Atlas.Fischer

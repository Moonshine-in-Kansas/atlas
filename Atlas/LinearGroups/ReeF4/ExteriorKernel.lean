import Atlas.LinearGroups.ReeF4.ExteriorSection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Dimension and an explicit retraction onto the domain of the partial product. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

section Ring
variable {F : Type*} [CommRing F] [CharP F 2]

def starProjectionLinear : (⋀[F]^2 (TraceZero F)) →ₗ[F] ⋀[F]^2 (TraceZero F) :=
  LinearMap.id - exteriorJointSection.comp exteriorJoint

theorem starProjection_mem (x : ⋀[F]^2 (TraceZero F)) :
    starProjectionLinear x ∈ StarCarrier (F := F) := by
  rw [starCarrier_eq_joint_ker, LinearMap.mem_ker]
  simp [starProjectionLinear, exteriorJoint_section]

def starProjection : (⋀[F]^2 (TraceZero F)) →ₗ[F] StarCarrier (F := F) :=
  starProjectionLinear.codRestrict _ starProjection_mem

@[simp] theorem starProjection_of_mem (x : StarCarrier (F := F)) :
    starProjection x.val = x := by
  apply Subtype.ext
  have hx : exteriorJoint x.val = 0 := by
    simpa [starCarrier_eq_joint_ker, LinearMap.mem_ker] using x.property
  simp [starProjection, starProjectionLinear, hx]

theorem starProjection_surjective : Function.Surjective (starProjection (F := F)) :=
  fun x => ⟨x.val, starProjection_of_mem x⟩

end Ring
section Field
variable {F : Type*} [Field F] [CharP F 2]

theorem exteriorSquare_finrank : Module.finrank F (⋀[F]^2 (TraceZero F)) = 325 := by
  rw [exteriorPower.finrank_eq, traceZero_finrank]
  decide

theorem starCarrier_finrank : Module.finrank F (StarCarrier (F := F)) = 298 := by
  have h := (exteriorJoint (F := F)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr exteriorJoint_surjective, finrank_top,
    Module.finrank_prod, Module.finrank_self, traceZero_finrank,
    exteriorSquare_finrank] at h
  rw [starCarrier_eq_joint_ker]
  omega

end Field
end Atlas.ReeF4

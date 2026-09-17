import Atlas.LinearGroups.Orthogonal.RootSubgroupCoordinates
import Atlas.LinearAlgebra.QuadraticComplementWitness

/-! # Root-group translations along a singular direction inside its perpendicular space -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V) (he : Q e = 0)

/-- A nonzero complement vector admits every prescribed polar pairing. -/
theorem complement_polar_surjective
    (hC : (complementForm Q e f).polarBilin.Nondegenerate)
    (w : complement Q e f) (hw : w ≠ 0) (a : F) :
    ∃ t : complement Q e f, Q.polarBilin w.val t.val = a := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : complement Q e f,
      (complementForm Q e f).polarBilin w t ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (hC.1 w h)
  have hwt : Q.polarBilin w.val t.val ≠ 0 := by
    rwa [complementForm_polar] at ht
  refine ⟨(a / Q.polarBilin w.val t.val) • t, ?_⟩
  change Q.polarBilin w.val ((a / Q.polarBilin w.val t.val) • t.val) = a
  rw [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ a hwt

/-- The singular-line root group freely changes the line coordinate above any
nonzero complement vector, using one actual Siegel transformation. -/
theorem root_transport_perpendicular_coordinate
    (hC : (complementForm Q e f).polarBilin.Nondegenerate)
    (w : complement Q e f) (hw : w ≠ 0) (c d : F) :
    ∃ r : isometrySubgroup Q, r ∈ rootSubgroup Q e he ∧
      r.val (c • e + w.val) = d • e + w.val := by
  obtain ⟨t, ht⟩ := complement_polar_surjective Q e f hC w hw (d-c)
  have het : Q.polarBilin e t.val = 0 := (polar_swap Q e t.val).trans t.prop.1
  have hwe : Q.polarBilin w.val e = 0 := w.prop.1
  have hee : Q.polarBilin e e = 0 := by rw [polar_self, he, mul_zero]
  have hxe : Q.polarBilin (c • e + w.val) e = 0 := by
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hee, smul_zero,
      hwe, add_zero]
  have hxt : Q.polarBilin (c • e + w.val) t.val = d-c := by
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, het, smul_zero,
      zero_add, ht]
  refine ⟨siegelElement Q e t.val he het,
    ⟨Multiplicative.ofAdd ⟨t.val, het⟩, rfl⟩, ?_⟩
  change siegel Q e t.val (c • e + w.val) = d • e + w.val
  rw [siegel, hxe, hxt, zero_smul, mul_zero, zero_smul, sub_zero, sub_zero]
  module

include he in
/-- The same transport belongs to the actual elementary group. -/
theorem elementary_transport_perpendicular_coordinate
    (hC : (complementForm Q e f).polarBilin.Nondegenerate)
    (w : complement Q e f) (hw : w ≠ 0) (c d : F) :
    ∃ r : isometrySubgroup Q, r ∈ elementarySubgroup Q ∧
      r.val (c • e + w.val) = d • e + w.val := by
  obtain ⟨r, hr, hrc⟩ := root_transport_perpendicular_coordinate Q e f he hC w hw c d
  exact ⟨r, rootSubgroup_le_elementary Q e he hr, hrc⟩

end Atlas.Orthogonal

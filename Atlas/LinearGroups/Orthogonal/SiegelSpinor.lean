import Atlas.LinearGroups.Orthogonal.SpinorNorm
import Mathlib.GroupTheory.Abelianization.Defs

/-! # Reflection factorization of Siegel transformations with anisotropic parameter -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u v : V) (hu : Q u = 0)
  (huv : Q.polarBilin u v = 0) (hv : Q v ≠ 0)

include hu huv in
theorem siegel_reflection_vector_value : Q (v + Q v • u) = Q v := by
  rw [Atlas.Quadratic.add_smul, hu, polar_swap Q v u, huv]
  ring

/-- A Siegel transformation is a product of two equal-norm reflections. -/
theorem siegelElement_reflection_factor :
    siegelElement Q u v hu huv =
      reflectionElement Q (v + Q v • u) (by rw [siegel_reflection_vector_value Q u v hu huv]; exact hv) *
        reflectionElement Q v hv := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hvu : Q.polarBilin v u = 0 := (polar_swap Q v u).trans huv
  have hp : Q.polarBilin (reflectionLinear Q v hv x) (v + Q v • u) =
      -Q.polarBilin x v + Q v * Q.polarBilin x u := by
    rw [reflectionLinear_apply]
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, polar_self, hvu, mul_zero, add_zero]
    field_simp
    ring
  change siegel Q u v x = reflectionLinear Q (v + Q v • u) (by rw [siegel_reflection_vector_value Q u v hu huv]; exact hv) (reflectionLinear Q v hv x)
  rw [reflectionLinear_apply, hp, reflectionLinear_apply, siegel_reflection_vector_value Q u v hu huv]
  simp only [siegel, mul_add, mul_neg, inv_mul_cancel₀ hv, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

theorem siegelElement_add (w : V) (huw : Q.polarBilin u w = 0) :
    siegelElement Q u v hu huv * siegelElement Q u w hu huw =
      siegelElement Q u (v+w) hu (by rw [map_add, huv, huw, add_zero]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact siegel_add Q u v w x hu huv huw

variable [FiniteDimensional F V] (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

/-- Every Siegel transformation has trivial intrinsic spinor norm, including isotropic parameters. -/
theorem spinorNorm_siegel : spinorNorm Q hQ h2 (siegelElement Q u v hu huv) = 1 := by
  let w := (2 : F)⁻¹ • v
  have huw : Q.polarBilin u w = 0 := by
    change Q.polarBilin u ((2 : F)⁻¹ • v) = 0
    rw [map_smul, huv, smul_zero]
  have hw : w+w = v := by
    change (2 : F)⁻¹ • v + (2 : F)⁻¹ • v = v
    rw [← _root_.add_smul]
    have hc : (2 : F)⁻¹ + (2 : F)⁻¹ = 1 := by field_simp; ring
    rw [hc, one_smul]
  have he : siegelElement Q u w hu huw * siegelElement Q u w hu huw =
      siegelElement Q u v hu huv := by
    rw [siegelElement_add]
    congr 1
  rw [← he, map_mul]
  obtain ⟨c, hc⟩ := Atlas.squareClass_surjective F
    (spinorNorm Q hQ h2 (siegelElement Q u w hu huw))
  rw [← hc, ← map_mul, ← pow_two, Atlas.squareClass_square]

/-- All elementary Siegel generators lie in the intrinsic spinor kernel. -/
theorem elementary_le_spinorKernel : elementarySubgroup Q ≤ (spinorNorm Q hQ h2).ker := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  exact spinorNorm_siegel Q u v hu huv hQ h2

/-- The full-group commutator subgroup lies in the intrinsic spinor kernel. -/
theorem commutator_le_spinorKernel :
    commutator (isometrySubgroup Q) ≤ (spinorNorm Q hQ h2).ker :=
  Abelianization.commutator_subset_ker (spinorNorm Q hQ h2)

/-- Both elementary and derived subgroups satisfy the two intrinsic kernel conditions. -/
theorem elementary_le_special_spinor : elementarySubgroup Q ≤
    specialSubgroup Q ⊓ (spinorNorm Q hQ h2).ker :=
  le_inf (elementary_le_special Q) (elementary_le_spinorKernel Q hQ h2)

theorem commutator_le_special_spinor : commutator (isometrySubgroup Q) ≤
    specialSubgroup Q ⊓ (spinorNorm Q hQ h2).ker :=
  le_inf (Abelianization.commutator_subset_ker (determinant Q))
    (commutator_le_spinorKernel Q hQ h2)

end Atlas.Orthogonal



import Atlas.LinearGroups.Orthogonal.DeterminantSign

/-! # Conjugation and scalar invariance of actual orthogonal reflections -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem reflectionElement_conj (g : isometrySubgroup Q) (a : V) (ha : Q a ≠ 0) :
    g * reflectionElement Q a ha * g⁻¹ =
      reflectionElement Q (g.val a) (by exact ne_of_eq_of_ne ((isometryCarrierEquiv Q g).map_app a) ha) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (reflectionLinear Q a ha (g.val.symm x)) = reflectionLinear Q (g.val a) (by exact ne_of_eq_of_ne ((isometryCarrierEquiv Q g).map_app a) ha) x
  rw [reflectionLinear_apply, reflectionLinear_apply, map_sub, map_smul, g.val.apply_symm_apply]
  have hq : Q (g.val a) = Q a := (isometryCarrierEquiv Q g).map_app a
  have hp := isometry_polar Q (isometryCarrierEquiv Q g) (g.val.symm x) a
  change Q.polarBilin (g.val (g.val.symm x)) (g.val a) = Q.polarBilin (g.val.symm x) a at hp
  rw [g.val.apply_symm_apply] at hp
  rw [hq, hp]

theorem reflectionElement_inv (a : V) (ha : Q a ≠ 0) :
    (reflectionElement Q a ha)⁻¹ = reflectionElement Q a ha := by
  apply Subtype.ext
  exact Module.reflection_symm (reflectionFunctional_self Q a ha)

theorem reflectionElement_square (a : V) (ha : Q a ≠ 0) :
    (reflectionElement Q a ha)^2 = 1 := by
  rw [pow_two]
  have h := inv_mul_cancel (reflectionElement Q a ha)
  rwa [reflectionElement_inv] at h

theorem reflectionElement_smul (a : V) (ha : Q a ≠ 0) (c : F) (hc : c ≠ 0) :
    reflectionElement Q (c • a) (by rw [Q.map_smul, smul_eq_mul]; exact mul_ne_zero (mul_ne_zero hc hc) ha) =
      reflectionElement Q a ha := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change reflectionLinear Q (c • a) (by rw [Q.map_smul, smul_eq_mul]; exact mul_ne_zero (mul_ne_zero hc hc) ha) x = reflectionLinear Q a ha x
  rw [reflectionLinear_apply, reflectionLinear_apply, Q.map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, smul_smul]
  match_scalars <;> field_simp <;> ring

end Atlas.Orthogonal

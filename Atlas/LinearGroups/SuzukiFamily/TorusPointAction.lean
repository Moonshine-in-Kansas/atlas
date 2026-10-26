import Atlas.LinearGroups.SuzukiFamily.ProjectiveAction
import Atlas.LinearGroups.SuzukiFamily.Torus

/-! Torus action on the projective ovoid in the column convention. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem torus_affine_vector (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (t : Fˣ) (a b : F) :
    h m t *ᵥ affineVector m a b =
      ((t:F)*theta F m (t:F)) • affineVector m
        (theta F m ((t⁻¹:Fˣ):F)*a)
        (((t⁻¹:Fˣ):F)^2*theta F m ((t⁻¹:Fˣ):F)*b) := by
  have ht : (t:F)≠0 := Units.ne_zero t
  have hθ : theta F m (t:F)≠0 := (map_ne_zero (theta F m)).mpr ht
  ext i
  fin_cases i <;>
    simp [h,affineVector,norm,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.diagonal_apply,Pi.smul_apply,-theta_apply,theta_square hcard,
      map_mul,map_pow,Units.val_inv_eq_inv_val] <;>
    field_simp <;> ring

theorem torus_affine (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (t : Fˣ) (a b : F) :
    pointLeft (torusElement m t) (affinePoint m a b)=
      affinePoint m (theta F m ((t⁻¹:Fˣ):F)*a)
        (((t⁻¹:Fˣ):F)^2*theta F m ((t⁻¹:Fˣ):F)*b) := by
  change Projectivization.mk F (matrix (torusElement m t) *ᵥ affineVector m a b) _ = _
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨Units.mk0 ((t:F)*theta F m (t:F))
    (mul_ne_zero (Units.ne_zero t) ((map_ne_zero (theta F m)).mpr (Units.ne_zero t))), ?_⟩
  simpa only [Units.smul_def,Units.val_mk0,matrix_torus] using
    (torus_affine_vector m hcard t a b).symm

theorem torus_infinity (m : ℕ) (t : Fˣ) :
    pointLeft (torusElement m t) (infinityPoint : Projective F)=infinityPoint := by
  change Projectivization.mk F (matrix (torusElement m t) *ᵥ infinityVector) _ = _
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨t⁻¹ * Units.map (theta F m).toMonoidHom t⁻¹, ?_⟩
  ext i
  fin_cases i <;> simp [matrix_torus,h,infinityVector,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,Matrix.diagonal_apply,Units.smul_def,-theta_apply]
end Atlas.SuzukiFamily

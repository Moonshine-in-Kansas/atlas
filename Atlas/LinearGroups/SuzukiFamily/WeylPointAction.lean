import Atlas.LinearGroups.SuzukiFamily.ProjectiveAction
import Atlas.LinearGroups.SuzukiFamily.Inversion

/-! Weyl inversion on the ovoid, using the anisotropic Suzuki norm. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem weyl_infinity_vector : w *ᵥ (infinityVector : Vector F)=affineVector 0 0 0 := by
  ext i
  fin_cases i <;> simp [w,infinityVector,affineVector,norm,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem weyl_infinity (m : ℕ) :
    pointLeft (weylElement : Atlas.Symplectic.Sp 2 F) infinityPoint=affinePoint m 0 0 := by
  change Projectivization.mk F (matrix weylElement *ᵥ infinityVector) _ = _
  simp only [matrix_weyl,weyl_infinity_vector]
  congr 1
  simp [affineVector,norm]

theorem weyl_origin (m : ℕ) :
    pointLeft (weylElement : Atlas.Symplectic.Sp 2 F) (affinePoint m 0 0)=infinityPoint := by
  have he : w *ᵥ affineVector (F := F) m 0 0=infinityVector := by
    ext i
    fin_cases i <;> simp [w,infinityVector,affineVector,norm,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  change Projectivization.mk F (matrix weylElement *ᵥ affineVector m 0 0) _ = _
  simp only [matrix_weyl,he]
  rfl

theorem weyl_affine_vector (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (hn : norm m a b ≠0) :
    w *ᵥ affineVector m a b =
      norm m a b • affineVector m (inverseFirst m a b) (inverseSecond m a b) := by
  ext i
  fin_cases i <;>
    simp [w,affineVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Pi.smul_apply,
      norm_inverse m hcard a b hn,hn,-theta_apply] <;>
    simp only [inverseFirst,inverseSecond] <;>
    field_simp <;> ring_nf <;> reduce_mod_char!

theorem weyl_affine (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (hn : norm m a b ≠0) :
    pointLeft (weylElement : Atlas.Symplectic.Sp 2 F) (affinePoint m a b)=
      affinePoint m (inverseFirst m a b) (inverseSecond m a b) := by
  change Projectivization.mk F (matrix weylElement *ᵥ affineVector m a b) _ = _
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨Units.mk0 (norm m a b) hn, ?_⟩
  simpa only [Units.smul_def,Units.val_mk0,matrix_weyl] using
    (weyl_affine_vector m hcard a b hn).symm
end Atlas.SuzukiFamily

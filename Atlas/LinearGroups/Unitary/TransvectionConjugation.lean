import Atlas.LinearGroups.Unitary.Transvections

/-! # Conjugation and scalar change of actual unitary transvections -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

theorem transvectionMatrix_smul (v : Fin n → K) (a c : K) :
    transvectionMatrix (F := F) (c • v) a =
      transvectionMatrix (F := F) v (a * (c * conjugation F K c)) := by
  ext i j
  simp only [transvectionMatrix, Matrix.add_apply, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, map_mul]
  ring

theorem transvectionMatrix_intertwine (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg) (v : Fin n → K) (a : K) :
    g.val * transvectionMatrix (F := F) v a =
      transvectionMatrix (F := F) (g.val *ᵥ v) a * g.val := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← mulVec_mulVec, ← mulVec_mulVec, transvectionMatrix_apply,
    transvectionMatrix_apply, mulVec_add, mulVec_smul]
  rw [u_preserves_hermitian hdeg (⟨g.val, g.prop.1⟩ : U F K n hdeg)]

theorem su_image_isotropic (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg) (v : Fin n → K) (hv : hermitian F K v v = 0) :
    hermitian F K (g.val *ᵥ v) (g.val *ᵥ v) = 0 :=
  (u_preserves_hermitian hdeg (⟨g.val, g.prop.1⟩ : U F K n hdeg) v v).trans hv

theorem transvection_conjugate (hdeg : Module.finrank F K = 2)
    (g : SU F K n hdeg) (v : Fin n → K) (a : K)
    (hv : hermitian F K v v = 0) (ha : a + conjugation F K a = 0) :
    g * transvection hdeg v a hv ha * g⁻¹ =
      transvection hdeg (g.val *ᵥ v) a (su_image_isotropic hdeg g v hv) ha := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  exact transvectionMatrix_intertwine hdeg g v a

end Atlas.Unitary

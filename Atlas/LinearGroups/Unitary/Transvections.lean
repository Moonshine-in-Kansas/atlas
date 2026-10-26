import Atlas.LinearGroups.Unitary.Hermitian
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Actual unitary line transvection matrices

The isotropy and trace-zero conditions are hypotheses on explicit vectors and
scalars. No generation or simplicity assertion is assumed here.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- The matrix of x ↦ x + a h(x,v) v. -/
def transvectionMatrix (v : Fin n → K) (a : K) : Matrix (Fin n) (Fin n) K :=
  1 + vecMulVec v (fun i => a * conjugation F K (v i))

theorem transvectionMatrix_apply (v x : Fin n → K) (a : K) :
    transvectionMatrix (F := F) v a *ᵥ x = x + (a * hermitian F K x v) • v := by
  rw [transvectionMatrix, add_mulVec, one_mulVec, vecMulVec_mulVec]
  ext i
  simp [dotProduct, hermitian, Finset.mul_sum, mul_comm, mul_left_comm]

theorem transvectionMatrix_det (v : Fin n → K) (a : K)
    (hv : hermitian F K v v = 0) : (transvectionMatrix (F := F) v a).det = 1 := by
  rw [transvectionMatrix, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]
  have he : (fun i => a * conjugation F K (v i)) ⬝ᵥ v = a * hermitian F K v v := by
    simp [dotProduct, hermitian, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [he, hv, mul_zero, add_zero]

theorem transvectionMatrix_preserves (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (a : K) (hv : hermitian F K v v = 0)
    (ha : a + conjugation F K a = 0) (x y : Fin n → K) :
    hermitian F K (transvectionMatrix (F := F) v a *ᵥ x)
      (transvectionMatrix (F := F) v a *ᵥ y) = hermitian F K x y := by
  rw [transvectionMatrix_apply, transvectionMatrix_apply]
  simp only [hermitian_add_left, hermitian_add_right, hermitian_smul_left,
    hermitian_smul_right, map_mul, hermitian_symmetry hdeg, hv, mul_zero, add_zero]
  have ha' : conjugation F K a = -a := by linear_combination ha
  rw [ha']
  ring

/-- This is an element of the retained full special unitary matrix carrier. -/
def transvection (hdeg : Module.finrank F K = 2) (v : Fin n → K) (a : K)
    (hv : hermitian F K v v = 0) (ha : a + conjugation F K a = 0) : SU F K n hdeg :=
  ⟨transvectionMatrix (F := F) v a,
    (mem_u_iff_preserves_hermitian hdeg _).mpr (transvectionMatrix_preserves hdeg v a hv ha),
    transvectionMatrix_det v a hv⟩

@[simp] theorem transvectionMatrix_zero (v : Fin n → K) :
    transvectionMatrix (F := F) v 0 = 1 := by
  ext i j
  simp [transvectionMatrix, vecMulVec]

theorem transvectionMatrix_mul (v : Fin n → K) (hv : hermitian F K v v = 0)
    (a b : K) : transvectionMatrix (F := F) v a * transvectionMatrix (F := F) v b =
      transvectionMatrix (F := F) v (a + b) := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← mulVec_mulVec, transvectionMatrix_apply, transvectionMatrix_apply,
    transvectionMatrix_apply]
  simp only [hermitian_add_left, hermitian_smul_left, hv, mul_zero, add_zero]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem transvectionMatrix_inverse (v : Fin n → K) (hv : hermitian F K v v = 0)
    (a : K) : transvectionMatrix (F := F) v a * transvectionMatrix (F := F) v (-a) = 1 := by
  rw [transvectionMatrix_mul v hv, add_neg_cancel, transvectionMatrix_zero]
end Atlas.Unitary

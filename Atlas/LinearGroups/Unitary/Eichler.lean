import Atlas.LinearGroups.Unitary.Transvections

/-! Actual unitary Eichler transformations, uniform in characteristic. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

def eichlerColumns (p w : Fin n → K) : Matrix (Fin n) (Fin 2) K := fun i => ![p i, w i]
def eichlerRows (p w : Fin n → K) (b : K) : Matrix (Fin 2) (Fin n) K :=
  ![fun i => b * conjugation F K (p i) - conjugation F K (w i),
    fun i => conjugation F K (p i)]
def eichlerMatrix (p w : Fin n → K) (b : K) : Matrix (Fin n) (Fin n) K :=
  1 + eichlerColumns p w * eichlerRows (F := F) p w b

theorem eichlerMatrix_apply (p w x : Fin n → K) (b : K) :
    eichlerMatrix (F := F) p w b *ᵥ x =
      x + (b * hermitian F K x p - hermitian F K x w) • p + hermitian F K x p • w := by
  rw [eichlerMatrix, add_mulVec, one_mulVec, ← mulVec_mulVec]
  ext i
  simp [eichlerColumns, eichlerRows, mulVec, dotProduct, Fin.sum_univ_succ,
    hermitian, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm, mul_left_comm]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, mul_comm, mul_left_comm, ← Finset.mul_sum]
  ring

theorem eichlerMatrix_det (hdeg : Module.finrank F K = 2)
    (p w : Fin n → K) (b : K) (hp : hermitian F K p p = 0)
    (hpw : hermitian F K p w = 0) : (eichlerMatrix (F := F) p w b).det = 1 := by
  have hwp : hermitian F K w p = 0 := by
    rw [← hermitian_symmetry hdeg p w, hpw, map_zero]
  simp only [hermitian] at hp hpw hwp
  have he : eichlerRows (F := F) p w b * eichlerColumns p w =
      !![0, -hermitian F K w w; 0, 0] := by
    ext i j
    change (∑ k : Fin n, eichlerRows (F := F) p w b i k * eichlerColumns p w k j) = _
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, eichlerRows, eichlerColumns, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
    all_goals simp [hp, hpw, hwp, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hermitian, mul_comm, mul_left_comm]
  rw [eichlerMatrix, det_one_add_mul_comm, he]
  simp [det_fin_two]

theorem eichlerMatrix_preserves (hdeg : Module.finrank F K = 2)
    (p w : Fin n → K) (b : K) (hp : hermitian F K p p = 0)
    (hpw : hermitian F K p w = 0)
    (hb : b + conjugation F K b + hermitian F K w w = 0) (x y : Fin n → K) :
    hermitian F K (eichlerMatrix (F := F) p w b *ᵥ x)
      (eichlerMatrix (F := F) p w b *ᵥ y) = hermitian F K x y := by
  have hwp : hermitian F K w p = 0 := by
    rw [← hermitian_symmetry hdeg p w, hpw, map_zero]
  rw [eichlerMatrix_apply, eichlerMatrix_apply]
  simp only [hermitian_add_left, hermitian_add_right, hermitian_smul_left,
    hermitian_smul_right, map_sub, map_mul, hermitian_symmetry hdeg,
    hp, hpw, hwp, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
  linear_combination hermitian F K x p * hermitian F K p y * hb

def eichler (hdeg : Module.finrank F K = 2)
    (p w : Fin n → K) (b : K) (hp : hermitian F K p p = 0)
    (hpw : hermitian F K p w = 0)
    (hb : b + conjugation F K b + hermitian F K w w = 0) : SU F K n hdeg :=
  ⟨eichlerMatrix p w b,
    (mem_u_iff_preserves_hermitian hdeg _).mpr (eichlerMatrix_preserves hdeg p w b hp hpw hb),
    eichlerMatrix_det hdeg p w b hp hpw⟩
end Atlas.Unitary

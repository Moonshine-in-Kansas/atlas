import Atlas.LinearAlgebra.RankOneMatrixTwo
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Nilpotent lines in determinant-one coordinates -/
noncomputable section
namespace Atlas.MatrixTwo
open Matrix
variable {F : Type*} [Field F]

theorem traceZero_singular_SL2_line (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M ≠ 0) (hd : M.det = 0) (ht : M.trace = 0) :
    ∃ A : SpecialLinearGroup (Fin 2) F, ∃ c : F, c ≠ 0 ∧
      M = A.val * !![0,c;0,0] * (A⁻¹).val := by
  obtain ⟨u,v,hu,hv,h⟩ := singular_nonzero_factor M hM hd
  let A := columnCompletion u hu
  let N := (A⁻¹).val * M * A.val
  have ht' : u 0 * v 0 + u 1 * v 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, h] using ht
  have hcol (i : Fin 2) : (M * A.val) i 0 = 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, A, columnCompletion_first, h]
    calc
      u i * v 0 * u 0 + u i * v 1 * u 1 =
          u i * (u 0 * v 0 + u 1 * v 1) := by ring
      _ = 0 := by rw [ht',mul_zero]
  have hncol (i : Fin 2) : N i 0 = 0 := by
    dsimp [N]
    rw [Matrix.mul_assoc]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hcol]
  have hntrace : N.trace = 0 := by
    change ((A⁻¹).val * M * A.val).trace = 0
    rw [Matrix.trace_mul_cycle, ← SpecialLinearGroup.coe_mul,
      mul_inv_cancel, SpecialLinearGroup.coe_one, one_mul]
    exact ht
  have h11 : N 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, hncol] using hntrace
  have hn : N = !![0,N 0 1;0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hncol,h11]
  have hrecover : A.val * N * (A⁻¹).val = M := by
    change A.val * ((A⁻¹).val * M * A.val) * (A⁻¹).val = M
    calc
      _ = (A.val * (A⁻¹).val) * M * (A.val * (A⁻¹).val) := by simp only [mul_assoc]
      _ = M := by rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel,
        SpecialLinearGroup.coe_one, one_mul, mul_one]
  refine ⟨A,N 0 1,?_,?_⟩
  · intro hc
    have hz : N = 0 := by rw [hn,hc]; ext i j; fin_cases i <;> fin_cases j <;> rfl
    apply hM
    simpa [hz] using hrecover.symm
  · rw [← hn]
    exact hrecover.symm
end Atlas.MatrixTwo

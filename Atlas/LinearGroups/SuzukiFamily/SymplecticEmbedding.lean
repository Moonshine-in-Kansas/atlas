import Atlas.LinearGroups.SuzukiFamily.Matrices
import Atlas.LinearGroups.Symplectic.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! The explicit basis permutation into the retained symplectic matrix group. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def coordinateIndex : (Fin 2 ⊕ Fin 2) ≃ Fin 4 where
  toFun := Sum.elim (fun i => ![0,1] i) (fun i => ![3,2] i)
  invFun := ![Sum.inl 0,Sum.inl 1,Sum.inr 1,Sum.inr 0]
  left_inv x := by rcases x with i | i <;> fin_cases i <;> rfl
  right_inv x := by fin_cases x <;> rfl

def toStandard : Matrix (Fin 4) (Fin 4) F ≃+* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.reindexRingEquiv F coordinateIndex.symm

@[simp] theorem toStandard_apply (A : Matrix (Fin 4) (Fin 4) F) (i j : Fin 2 ⊕ Fin 2) :
    toStandard A i j = A (coordinateIndex i) (coordinateIndex j) := rfl

theorem u_symplectic (m : ℕ) (a b : F) :
    toStandard (u m a b) ∈ Matrix.symplecticGroup (Fin 2) F := by
  rw [SymplecticGroup.mem_iff']
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.J,
      Matrix.fromBlocks,Matrix.one_apply,coordinateIndex,u,norm,-theta_apply] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

theorem w_symplectic :
    toStandard (w : Matrix (Fin 4) (Fin 4) F) ∈ Matrix.symplecticGroup (Fin 2) F := by
  rw [SymplecticGroup.mem_iff']
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.J,
      Matrix.fromBlocks,Matrix.one_apply,coordinateIndex,w] <;> reduce_mod_char!
end Atlas.SuzukiFamily

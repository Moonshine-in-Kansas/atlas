import Atlas.LinearGroups.Unitary.TransvectionCommutator
import Atlas.LinearGroups.Unitary.PointNormalClosure
import Mathlib.Algebra.CharP.Two
import Mathlib.GroupTheory.IsPerfect

/-! Exact commutator identity for the binary rank-four perfectness base. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped commutatorElement
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable [CharP K 2]

def binaryCommVectors (c : K) : Fin 4 → (Fin 4 → K) :=
  ![![1,1,c,c], ![1,1,1,1], ![1,1,c,c^2], ![0,0,1,c]]

def binaryCommTarget : Fin 4 → K := ![1,1,0,0]

set_option maxHeartbeats 2000000 in
theorem binaryComm_matrix_relation (hq : Nat.card F = 2) (c : K)
    (hc : c^2+c+1=0) :
    (transvectionMatrix (F := F) (binaryCommVectors c 0) 1 *
      transvectionMatrix (F := F) (binaryCommVectors c 1) 1) *
    (transvectionMatrix (F := F) (binaryCommVectors c 2) 1 *
      transvectionMatrix (F := F) (binaryCommVectors c 3) 1) =
    transvectionMatrix (F := F) binaryCommTarget 1 *
    (transvectionMatrix (F := F) (binaryCommVectors c 2) 1 *
      transvectionMatrix (F := F) (binaryCommVectors c 3) 1) *
    (transvectionMatrix (F := F) (binaryCommVectors c 0) 1 *
      transvectionMatrix (F := F) (binaryCommVectors c 1) 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hA : transvectionMatrix (F := F) (binaryCommVectors c 0) 1 *
      transvectionMatrix (F := F) (binaryCommVectors c 1) 1 =
      !![1,0,c,c; 0,1,c,c; c^2,c^2,1,0; c^2,c^2,0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [transvectionMatrix, binaryCommVectors, Matrix.mul_apply, vecMulVec,
        Fin.sum_univ_four, conjugation_apply, hq, Matrix.one_apply,
        Matrix.cons_val_two, Matrix.cons_val_three] <;> grind
  have hB : transvectionMatrix (F := F) (binaryCommVectors c 2) 1 *
      transvectionMatrix (F := F) (binaryCommVectors c 3) 1 =
      !![0,1,c^2,c; 1,0,c^2,c; c,c,1,0; c^2,c^2,0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [transvectionMatrix, binaryCommVectors, Matrix.mul_apply, vecMulVec,
        Fin.sum_univ_four, conjugation_apply, hq, Matrix.one_apply,
        Matrix.cons_val_two, Matrix.cons_val_three] <;> grind
  rw [hA,hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transvectionMatrix, binaryCommTarget, Matrix.mul_apply, vecMulVec,
      Fin.sum_univ_four, conjugation_apply, hq, Matrix.one_apply,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> grind

theorem binaryComm_isotropic (hq : Nat.card F = 2) (c : K)
    (hc : c^2+c+1=0) (i : Fin 4) : hermitian F K (binaryCommVectors c i) (binaryCommVectors c i) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  fin_cases i <;>
    norm_num [hermitian, binaryCommVectors, Fin.sum_univ_four, conjugation_apply, hq,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> grind

theorem binaryCommTarget_isotropic (hq : Nat.card F = 2) :
    hermitian F K (binaryCommTarget : Fin 4 → K) binaryCommTarget = 0 := by
  simp [hermitian, binaryCommTarget, Fin.sum_univ_four, conjugation_apply, hq,
    Matrix.cons_val_two, Matrix.cons_val_three, CharTwo.add_self_eq_zero]

theorem binaryComm_target_mem_commutator (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) (c : K) (hc : c^2+c+1=0) :
    transvection hdeg binaryCommTarget 1 (binaryCommTarget_isotropic hq)
      (by simp [CharTwo.add_self_eq_zero]) ∈ commutator (SU F K 4 hdeg) := by
  have htrace : (1 : K) + conjugation F K 1 = 0 := by simp [CharTwo.add_self_eq_zero]
  let t (i : Fin 4) := transvection hdeg (binaryCommVectors c i) 1 (binaryComm_isotropic hq c hc i) htrace
  let s := transvection hdeg binaryCommTarget 1 (binaryCommTarget_isotropic hq) htrace
  have hrel : (t 0 * t 1) * (t 2 * t 3) = s * (t 2 * t 3) * (t 0 * t 1) := by
    apply Subtype.ext
    exact binaryComm_matrix_relation hq c hc
  have he : ⁅t 0 * t 1, t 2 * t 3⁆ = s := by
    rw [commutatorElement_def, hrel]
    group
  change s ∈ commutator (SU F K 4 hdeg)
  rw [← he, commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet _ _)

theorem binary_trace_zero_cases (hq : Nat.card F = 2) (a : K)
    (ha : a + conjugation F K a = 0) : a = 0 ∨ a = 1 := by
  rw [conjugation_apply, hq] at ha
  have hprod : a * (a + 1) = 0 := by linear_combination ha
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl h
  · right
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h - h2

/-- The binary rank-four perfectness step, explicitly conditional on the
separate generation theorem. The final family theorem will discharge it. -/
theorem special_four_perfect_of_binary_generated (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) (c : K) (hc : c^2+c+1=0)
    (hgen : transvectionGenerated hdeg (n := 4) = ⊤) :
    Group.IsPerfect (SU F K 4 hdeg) := by
  let v : Fin 4 → K := binaryCommTarget
  have hv : v ≠ 0 := by intro he; have := congrFun he 0; simpa [v,binaryCommTarget] using this
  have hvv : hermitian F K v v = 0 := binaryCommTarget_isotropic hq
  let p := isotropicPoint v hv hvv
  have hp : pointTransvections hdeg p = lineTransvections hdeg v hvv := by
    apply lineTransvections_eq_of_projective_eq hdeg _ _ _ _ p.val.rep_nonzero hv
    exact Projectivization.mk_rep p.val
  have hle : pointTransvections hdeg p ≤ commutator (SU F K 4 hdeg) := by
    rw [hp]
    rintro g ⟨a,rfl⟩
    have ha := (trace_zero_iff hdeg a.toAdd.val).mp a.toAdd.prop
    rcases binary_trace_zero_cases hq a.toAdd.val ha with hz | ho
    · have he : lineTransvectionHom hdeg v hvv a = 1 := by
        apply Subtype.ext
        change transvectionMatrix (F := F) v a.toAdd.val = 1
        rw [hz, transvectionMatrix_zero]
      rw [he]
      exact Subgroup.one_mem _
    · have he : lineTransvectionHom hdeg v hvv a =
          transvection hdeg binaryCommTarget 1 (binaryCommTarget_isotropic hq)
            (by simp [CharTwo.add_self_eq_zero]) := by
        apply Subtype.ext
        change transvectionMatrix (F := F) v a.toAdd.val = _
        rw [ho]
        rfl
      rw [he]
      exact binaryComm_target_mem_commutator hdeg hq c hc
  have hcl := Subgroup.normalClosure_le_normal hle
  rw [normalClosure_pointTransvections, hgen] at hcl
  exact ⟨top_unique hcl⟩
end Atlas.Unitary

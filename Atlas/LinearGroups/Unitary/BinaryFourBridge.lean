import Atlas.LinearGroups.Unitary.GeneratedNormal
import Atlas.LinearGroups.Unitary.SpecialStabilizer
import Mathlib.Algebra.CharP.Two

/-! # A short binary rank-four transvection bridge

The matrix fixing the first coordinate and acting by the three-dimensional
Fourier matrix on its complement is a product of four genuine transvections.
The candidate word was found by a small bounded matrix search; the identities
below are proved symbolically by the kernel, with no external certificate.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable [CharP K 2]

/-- The nonmonomial binary SU₃ Fourier matrix. -/
def binaryFourierThree (c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1,1,1; 1,c,c^2; 1,c^2,c]

def binaryBridgeVector (c : K) : Fin 4 → (Fin 4 → K) :=
  ![![1,c^2,0,0], ![1,1,0,0], ![1,c,c^2,c^2], ![1,1,c,c]]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem binaryBridge_word (hq : Nat.card F = 2) (c : K) (hc : c ^ 2 + c + 1 = 0) :
    transvectionMatrix (F := F) (binaryBridgeVector c 0) 1 *
      transvectionMatrix (F := F) (binaryBridgeVector c 1) 1 *
      transvectionMatrix (F := F) (binaryBridgeVector c 2) 1 *
      transvectionMatrix (F := F) (binaryBridgeVector c 3) 1 =
        extendMatrix (binaryFourierThree c) := by
  have h2 : c ^ 2 = c + 1 := by
    rw [← CharTwo.neg_eq (c + 1), neg_add_rev]
    linear_combination hc
  have h3 : c ^ 3 = 1 := by
    calc
      c ^ 3 = c ^ 2 * c := by ring
      _ = (c + 1) * c := congrArg (fun z : K => z * c) h2
      _ = c ^ 2 + c := by ring
      _ = (c + 1) + c := congrArg (fun z : K => z + c) h2
      _ = (c + c) + 1 := by ring
      _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
  have hc2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc3 : (3 : K) = 1 := by linear_combination hc2
  have hc4 : (4 : K) = 0 := by linear_combination 2 * hc2
  have hc5 : (5 : K) = 1 := by linear_combination 2 * hc2
  have hc6 : (6 : K) = 0 := by linear_combination 3 * hc2
  have hc7 : (7 : K) = 1 := by linear_combination 3 * hc2
  have hc8 : (8 : K) = 0 := by linear_combination 4 * hc2
  have hc9 : (9 : K) = 1 := by linear_combination 4 * hc2
  have hc10 : (10 : K) = 0 := by linear_combination 5 * hc2
  have hc12 : (12 : K) = 0 := by linear_combination 6 * hc2
  have hc16 : (16 : K) = 0 := by linear_combination 8 * hc2
  have hp (k : ℕ) : c ^ (k + 3) = c ^ k := by rw [pow_add, h3, mul_one]
  have hp4 : c ^ 4 = c := by
    calc
      c ^ 4 = c ^ 1 := hp 1
      _ = _ := by simp only [h3, pow_one, pow_zero]
  have hp5 : c ^ 5 = c ^ 2 := by
    calc
      c ^ 5 = c ^ 2 := hp 2
      _ = _ := by simp only [h3, hp4, pow_one, pow_zero]
  have hp6 : c ^ 6 = 1 := by
    calc
      c ^ 6 = c ^ 3 := hp 3
      _ = _ := by simp only [h3, hp4, hp5, pow_one, pow_zero]
  have hp7 : c ^ 7 = c := by
    calc
      c ^ 7 = c ^ 4 := hp 4
      _ = _ := by simp only [h3, hp4, hp5, hp6, pow_one, pow_zero]
  have hp8 : c ^ 8 = c ^ 2 := by
    calc
      c ^ 8 = c ^ 5 := hp 5
      _ = _ := by simp only [h3, hp4, hp5, hp6, hp7, pow_one, pow_zero]
  have hp9 : c ^ 9 = 1 := by
    calc
      c ^ 9 = c ^ 6 := hp 6
      _ = _ := by simp only [h3, hp4, hp5, hp6, hp7, hp8, pow_one, pow_zero]
  have hp10 : c ^ 10 = c := by
    calc
      c ^ 10 = c ^ 7 := hp 7
      _ = _ := by simp only [h3, hp4, hp5, hp6, hp7, hp8, hp9, pow_one, pow_zero]
  have hp11 : c ^ 11 = c ^ 2 := by
    calc
      c ^ 11 = c ^ 8 := hp 8
      _ = _ := by simp only [h3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, pow_one, pow_zero]
  have hp12 : c ^ 12 = 1 := by
    calc
      c ^ 12 = c ^ 9 := hp 9
      _ = _ := by simp only [h3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, pow_one, pow_zero]
  have hA : transvectionMatrix (F := F) (binaryBridgeVector c 0) 1 *
      transvectionMatrix (F := F) (binaryBridgeVector c 1) 1 =
      !![c,0,0,0; 0,c^2,0,0; 0,0,1,0; 0,0,0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [transvectionMatrix, binaryBridgeVector, mul_apply, vecMulVec,
        Fin.sum_univ_four, conjugation_apply, hq, Matrix.one_apply, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk] <;>
      grind
  have hB : transvectionMatrix (F := F) (binaryBridgeVector c 2) 1 *
      transvectionMatrix (F := F) (binaryBridgeVector c 3) 1 =
      !![c^2,0,0,0; 0,c,c,c; 0,1,c,c^2; 0,1,c^2,c] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [transvectionMatrix, binaryBridgeVector, mul_apply, vecMulVec,
        Fin.sum_univ_four, conjugation_apply, hq, Matrix.one_apply, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk] <;>
      grind
  have hext : extendMatrix (binaryFourierThree c) =
      !![1,0,0,0; 0,1,1,1; 0,1,c,c^2; 0,1,c^2,c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hext]
  rw [mul_assoc _ (transvectionMatrix (F := F) (binaryBridgeVector c 2) 1), hA, hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryFourierThree, extendMatrix, mul_apply, Fin.sum_univ_four,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk] <;> grind

theorem binaryBridge_isotropic (hq : Nat.card F = 2) (c : K)
    (hc : c ^ 2 + c + 1 = 0) (i : Fin 4) :
    hermitian F K (binaryBridgeVector c i) (binaryBridgeVector c i) = 0 := by
  have hc2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : c ^ 3 = 1 := by
    have h : (c - 1) * (c ^ 2 + c + 1) = c ^ 3 - 1 := by ring
    rw [hc, mul_zero] at h
    exact sub_eq_zero.mp h.symm
  have h6 : c ^ 6 = 1 := by
    calc
      c ^ 6 = c ^ 3 * c ^ 3 := by ring
      _ = 1 := by rw [h3, one_mul]
  fin_cases i <;>
    norm_num [binaryBridgeVector, hermitian, Fin.sum_univ_four, Fin.reduceFinMk,
      conjugation_apply, hq] <;> try ring_nf <;> simp [h3, h6, hc2, CharTwo.add_self_eq_zero]

/-- The bridge word consists of actual elements of the generated subgroup. -/
def binaryBridgeElement (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (c : K) (hc : c ^ 2 + c + 1 = 0) : SU F K 4 hdeg :=
  transvection hdeg (binaryBridgeVector c 0) 1 (binaryBridge_isotropic hq c hc 0)
    (by simp [CharTwo.add_self_eq_zero]) *
  transvection hdeg (binaryBridgeVector c 1) 1 (binaryBridge_isotropic hq c hc 1)
    (by simp [CharTwo.add_self_eq_zero]) *
  transvection hdeg (binaryBridgeVector c 2) 1 (binaryBridge_isotropic hq c hc 2)
    (by simp [CharTwo.add_self_eq_zero]) *
  transvection hdeg (binaryBridgeVector c 3) 1 (binaryBridge_isotropic hq c hc 3)
    (by simp [CharTwo.add_self_eq_zero])

theorem binaryBridgeElement_matrix (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (c : K) (hc : c ^ 2 + c + 1 = 0) :
    (binaryBridgeElement hdeg hq c hc).val = extendMatrix (binaryFourierThree c) :=
  binaryBridge_word hq c hc

theorem binaryBridgeElement_generated (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (c : K) (hc : c ^ 2 + c + 1 = 0) :
    binaryBridgeElement hdeg hq c hc ∈ transvectionGenerated hdeg := by
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem <;> exact transvection_mem_generated _ _ _ _ _
    · exact transvection_mem_generated _ _ _ _ _
  · exact transvection_mem_generated _ _ _ _ _

end Atlas.Unitary

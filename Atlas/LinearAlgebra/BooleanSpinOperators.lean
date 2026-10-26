import Atlas.LinearAlgebra.BooleanSpinSigns
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Creation, annihilation and parity on literal Boolean labels.
All identities are over CommRing and proved on singleton columns, uniformly in rank. -/
noncomputable section
namespace Atlas.BooleanSpin
open Classical
variable {I : Type*} [Fintype I] [LinearOrder I]
variable (R : Type*) [CommRing R]

abbrev Space := (I → Bool) →₀ R

def step (i : I) (b : Bool) : Module.End R (Space (I := I) R) :=
  Finsupp.linearCombination R fun σ =>
    if σ i = b then 0 else Finsupp.single (flip i σ) («prefix» R i σ)

abbrev creation (i : I) := step R i true
abbrev annihilation (i : I) := step R i false

def parity : Module.End R (Space (I := I) R) :=
  Finsupp.linearCombination R fun σ => Finsupp.single σ (paritySign R σ)

@[simp] theorem step_single (i : I) (b : Bool) (σ : I → Bool) (r : R) :
    step R i b (Finsupp.single σ r) =
      if σ i = b then 0 else Finsupp.single (flip i σ) («prefix» R i σ*r) := by
  by_cases h : σ i = b <;> simp [step, h, Finsupp.smul_single, mul_comm]

@[simp] theorem parity_single (σ : I → Bool) (r : R) :
    parity (I := I) R (Finsupp.single σ r) = Finsupp.single σ (paritySign R σ*r) := by
  simp [parity, Finsupp.smul_single, mul_comm]

theorem step_square (i : I) (b : Bool) : step R i b * step R i b = 0 := by
  apply Finsupp.lhom_ext
  intro σ r
  cases h : σ i <;> cases b <;>
    simp [Module.End.mul_apply, step_single, h]

theorem creation_annihilation (i : I) :
    creation R i * annihilation R i + annihilation R i * creation R i = 1 := by
  apply Finsupp.lhom_ext
  intro σ r
  cases h : σ i <;>
    simp [creation, annihilation, Module.End.mul_apply, step_single, h,
      ← mul_assoc, prefix_mul_self]

private theorem step_anticomm_of_lt (i j : I) (hij : i < j) (b c : Bool) :
    step R i b * step R j c = -(step R j c * step R i b) := by
  apply Finsupp.lhom_ext
  intro σ r
  have hne : i ≠ j := ne_of_lt hij
  by_cases hi : σ i = b <;> by_cases hj : σ j = c <;>
    simp [Module.End.mul_apply, step_single, hi, hj, hne, Ne.symm hne,
      prefix_flip, hij, not_lt_of_ge (le_of_lt hij), flip_comm i j hne,
      ← Finsupp.single_neg, mul_comm, mul_left_comm, mul_assoc]

theorem step_anticomm (i j : I) (hij : i ≠ j) (b c : Bool) :
    step R i b * step R j c = -(step R j c * step R i b) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact step_anticomm_of_lt R i j h b c
  · apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro k
    have he := congrArg (fun f : Module.End R (Space (I := I) R) => f v k)
      (step_anticomm_of_lt R j i h c b)
    simp only [LinearMap.neg_apply, Finsupp.neg_apply] at he ⊢
    linear_combination he

theorem parity_square : parity (I := I) R * parity R = 1 := by
  apply Finsupp.lhom_ext
  intro σ r
  simp [Module.End.mul_apply, ← mul_assoc, paritySign_mul_self]

theorem parity_step (i : I) (b : Bool) :
    parity R * step R i b = -(step R i b * parity R) := by
  apply Finsupp.lhom_ext
  intro σ r
  by_cases h : σ i = b <;>
    simp [Module.End.mul_apply, step_single, h, ← Finsupp.single_neg,
      mul_comm, mul_left_comm, mul_assoc]

theorem parity_eq_one_of_two_eq_zero (h2 : (2 : R) = 0) : parity (I := I) R = 1 := by
  have hneg : (-1 : R) = 1 := by linear_combination -h2
  have hs (σ : I → Bool) : paritySign R σ = 1 := by
    simp [paritySign, signProduct, bitSign, hneg]
  apply Finsupp.lhom_ext
  intro σ r
  simp [hs]

theorem creation_annihilation_adjacent_single (n : ℕ) (i : Fin n)
    (σ : Fin (n+1) → Bool) (r : R) :
    creation R i.castSucc (annihilation R i.succ (Finsupp.single σ r)) =
      if σ i.castSucc = false ∧ σ i.succ = true then
        Finsupp.single (Function.update (Function.update σ i.succ false) i.castSucc true) r
      else 0 := by
  have hij : i.castSucc < i.succ := i.castSucc_lt_succ
  have hne : i.castSucc ≠ i.succ := ne_of_lt hij
  cases hi : σ i.castSucc <;> cases hj : σ i.succ <;>
    simp [creation, annihilation, step_single, hi, hj, hne, Ne.symm hne,
      prefix_flip, hij, not_lt_of_ge (le_of_lt hij), prefix_adjacent, bitSign,
      ← mul_assoc, prefix_mul_self] <;>
    simp [flip, hi, hj, hne, Ne.symm hne]

theorem creation_annihilation_adjacent_reverse_single (n : ℕ) (i : Fin n)
    (σ : Fin (n+1) → Bool) (r : R) :
    creation R i.succ (annihilation R i.castSucc (Finsupp.single σ r)) =
      if σ i.castSucc = true ∧ σ i.succ = false then
        Finsupp.single (Function.update (Function.update σ i.succ true) i.castSucc false) r
      else 0 := by
  have hij : i.castSucc < i.succ := i.castSucc_lt_succ
  have hne : i.castSucc ≠ i.succ := ne_of_lt hij
  cases hi : σ i.castSucc <;> cases hj : σ i.succ <;>
    simp [creation, annihilation, step_single, hi, hj, hne, Ne.symm hne,
      prefix_flip, hij, not_lt_of_ge (le_of_lt hij), prefix_adjacent, bitSign,
      ← mul_assoc, prefix_mul_self] <;>
    simp [flip, hi, hj, hne, Ne.symm hne, Function.update_comm hne]

theorem creation_parity_last_single (n : ℕ) (σ : Fin (n+1) → Bool) (r : R) :
    creation R (Fin.last n) (parity R (Finsupp.single σ r)) =
      if σ (Fin.last n) = false then Finsupp.single (Function.update σ (Fin.last n) true) r
      else 0 := by
  cases h : σ (Fin.last n) <;>
    simp [creation, step_single, paritySign_last, bitSign, h,
      ← mul_assoc, prefix_mul_self] <;> simp [flip, h]

theorem parity_annihilation_last_single (n : ℕ) (σ : Fin (n+1) → Bool) (r : R) :
    parity R (annihilation R (Fin.last n) (Finsupp.single σ r)) =
      if σ (Fin.last n) = true then Finsupp.single (Function.update σ (Fin.last n) false) r
      else 0 := by
  cases h : σ (Fin.last n) <;>
    simp [annihilation, step_single, paritySign_last, bitSign, h,
      ← mul_assoc, prefix_mul_self] <;> simp [flip, h]

def matrix : Module.End R (Space (I := I) R) ≃ₐ[R] Matrix (I → Bool) (I → Bool) R :=
  LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne

@[simp] theorem matrix_apply (f : Module.End R (Space (I := I) R)) (σ τ : I → Bool) :
    matrix R f σ τ = f (Finsupp.single τ 1) σ := by
  simp [matrix, LinearMap.toMatrixAlgEquiv_apply]

end Atlas.BooleanSpin

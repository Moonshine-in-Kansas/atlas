import Atlas.Lattices.ConwayWales.Coordinates
import Mathlib.Data.Matrix.Mul

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Matrix

@[simp] theorem dagger_add (x y : Q) : dagger (x + y) = dagger x + dagger y := by
  ext <;> simp [dagger, neg_add, add_comm]

@[simp] theorem dagger_smul (z : ℂ) (x : Q) : dagger (z • x) = star z • dagger x := by
  ext <;> simp [dagger]

theorem dagger_mul (x y : Q) : dagger (x * y) = dagger y * dagger x := by
  ext <;> simp [dagger] <;> ring

theorem shifted_correlation (r t : Row) :
    (∑ s : Row, coefficient (r + s) * coefficient (s + t)) =
      if t = r then 16 else 0 := by
  calc
    _ = ∑ u : Row, coefficient u * coefficient (u + (t - r)) := by
      apply Fintype.sum_bijective (fun s : Row => r + s) (Equiv.addLeft r).bijective
      intro s
      congr 2
      abel
    _ = _ := by rw [correlation]; simp only [sub_eq_zero]

def convolutionMatrix : Matrix Row Row Q := fun r s => (1 / 4 : ℂ) • coefficient (r + s)

theorem convolution_eq_mulVec (v : Space) : convolution v = convolutionMatrix *ᵥ v := by
  funext r
  simp [convolution, convolutionMatrix, Matrix.mulVec, dotProduct,
    Finset.smul_sum, smul_mul_assoc]

theorem convolutionMatrix_sq : convolutionMatrix * convolutionMatrix = 1 := by
  funext r t
  simp only [Matrix.mul_apply, convolutionMatrix, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← Finset.smul_sum]
  rw [shifted_correlation]
  by_cases h : t = r
  · subst t
    simp only [ite_true, Matrix.one_apply, if_pos rfl]
    ext <;> norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  · simp [h, Matrix.one_apply, Ne.symm h]

theorem convolution_involutive : Function.Involutive convolution := by
  intro v
  simp only [convolution_eq_mulVec, Matrix.mulVec_mulVec, convolutionMatrix_sq,
    Matrix.one_mulVec]

theorem convolution_right_mul (v : Space) (u : Q) :
    convolution (fun r => v r * u) = fun r => convolution v r * u := by
  funext r
  simp [convolution, Finset.sum_mul, mul_assoc, smul_mul_assoc]

theorem convolution_add (v w : Space) : convolution (v + w) = convolution v + convolution w := by
  funext r
  simp [convolution, mul_add, Finset.sum_add_distrib, smul_add]

theorem convolution_smul (z : ℂ) (v : Space) : convolution (z • v) = z • convolution v := by
  funext r
  simp only [convolution, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum]
  exact smul_comm _ _ _


def rowPair (x y : Q) : ℂ := (dagger x * y).re

@[simp] theorem rowPair_zero_left (y : Q) : rowPair 0 y = 0 := by simp [rowPair, dagger]
@[simp] theorem rowPair_zero_right (x : Q) : rowPair x 0 = 0 := by simp [rowPair]
@[simp] theorem rowPair_add_left (x y z : Q) : rowPair (x + y) z = rowPair x z + rowPair y z := by
  simp [rowPair, add_mul]
@[simp] theorem rowPair_add_right (x y z : Q) : rowPair x (y + z) = rowPair x y + rowPair x z := by
  simp [rowPair, mul_add]
@[simp] theorem rowPair_smul_left (z : ℂ) (x y : Q) : rowPair (z • x) y = star z * rowPair x y := by
  simp [rowPair, smul_mul_assoc]
@[simp] theorem rowPair_smul_right (z : ℂ) (x y : Q) : rowPair x (z • y) = z * rowPair x y := by
  simp [rowPair, mul_smul_comm]

theorem rowPair_sum_left {ι : Type*} (s : Finset ι) (v : ι → Q) (y : Q) :
    rowPair (∑ i ∈ s, v i) y = ∑ i ∈ s, rowPair (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem rowPair_sum_right {ι : Type*} (s : Finset ι) (x : Q) (v : ι → Q) :
    rowPair x (∑ i ∈ s, v i) = ∑ i ∈ s, rowPair x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem rowPair_mul_left (q x y : Q) : rowPair (q * x) y = rowPair x (dagger q * y) := by
  simp only [rowPair, dagger_mul, mul_assoc]

theorem convolution_self_adjoint (v w : Space) :
    hermitian (convolution v) w = hermitian v (convolution w) := by
  change (∑ r, rowPair (convolution v r) (w r)) = ∑ r, rowPair (v r) (convolution w r)
  simp only [convolution, rowPair_smul_left, rowPair_smul_right,
    rowPair_sum_left, rowPair_sum_right, map_div₀, map_one, map_ofNat, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  rw [rowPair_mul_left, coefficient_self_adjoint]
  rw [add_comm r s]
  norm_num

theorem convolution_unitary (v w : Space) :
    hermitian (convolution v) (convolution w) = hermitian v w := by
  rw [convolution_self_adjoint, convolution_involutive w]

/-- The actual ambient complex-linear involution; lattice preservation is not assumed. -/
def convolutionLinearEquiv : Space ≃ₗ[ℂ] Space where
  toFun := convolution
  invFun := convolution
  left_inv := convolution_involutive
  right_inv := convolution_involutive
  map_add' := convolution_add
  map_smul' := convolution_smul

end Atlas.ConwayWales


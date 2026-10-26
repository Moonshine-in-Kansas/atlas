import Atlas.LinearGroups.Symplectic.Transvection
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! Paired elementary matrices inside the established symplectic carrier. -/
noncomputable section
namespace Atlas.Symplectic
open Matrix
variable (r : ℕ) (R : Type*) [CommRing R]

/-- The genuine contragredient block action of SL on a hyperbolic space. -/
def diagonalSLHom : Matrix.SpecialLinearGroup (Fin r) R →* Sp r R where
  toFun g := ⟨Matrix.fromBlocks g.val 0 0 (g⁻¹).val.transpose, by
    apply _root_.SymplecticGroup.fromBlocks_mem_iff.mpr
    refine ⟨by simp, by simp, ?_⟩
    have hi : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
    simpa only [Matrix.transpose_mul, Matrix.transpose_one, Matrix.transpose_zero,
      zero_mul, sub_zero] using congrArg Matrix.transpose hi⟩
  map_one' := by apply Subtype.ext; simp [Matrix.fromBlocks_one]
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.fromBlocks (g * h).val 0 0 ((g * h)⁻¹).val.transpose =
      Matrix.fromBlocks g.val 0 0 (g⁻¹).val.transpose *
        Matrix.fromBlocks h.val 0 0 (h⁻¹).val.transpose
    simp only [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
      Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add]

def pairedTransvection {i j : Fin r} (hij : i ≠ j) (t : R) : Sp r R :=
  diagonalSLHom r R (Matrix.SpecialLinearGroup.transvection hij t)

theorem pairedTransvection_matrix {i j : Fin r} (hij : i ≠ j) (t : R) :
    (pairedTransvection r R hij t).val = Matrix.fromBlocks
      (Matrix.transvection i j t) 0 0 (Matrix.transvection j i (-t)) := by
  change Matrix.fromBlocks (Matrix.SpecialLinearGroup.transvection hij t).val 0 0
    ((Matrix.SpecialLinearGroup.transvection hij t)⁻¹).val.transpose = _
  rw [Matrix.SpecialLinearGroup.transvection_inv]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single]

theorem pairedTransvection_inl {i j : Fin r} (hij : i ≠ j) (t : R)
    (x : Vector r R) (k : Fin r) :
    (pairedTransvection r R hij t • x) (.inl k) =
      x (.inl k) + if k = i then t * x (.inl j) else 0 := by
  rw [smul_eq_mulVec, pairedTransvection_matrix, Matrix.fromBlocks_mulVec]
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec,
    Function.update_apply, eq_comm]

theorem pairedTransvection_inr {i j : Fin r} (hij : i ≠ j) (t : R)
    (x : Vector r R) (k : Fin r) :
    (pairedTransvection r R hij t • x) (.inr k) =
      x (.inr k) - if k = j then t * x (.inr i) else 0 := by
  rw [smul_eq_mulVec, pairedTransvection_matrix, Matrix.fromBlocks_mulVec]
  by_cases hk : k = j
  · subst k
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec,
      Function.update_apply, sub_eq_add_neg]
  · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec,
      Function.update_apply, sub_eq_add_neg, hk, Ne.symm hk]

def pairedWeyl {i j : Fin r} (hij : i ≠ j) : Sp r R :=
  pairedTransvection r R hij 1 * pairedTransvection r R (Ne.symm hij) (-1) *
    pairedTransvection r R hij 1

theorem pairedWeyl_e {i j : Fin r} (hij : i ≠ j) :
    pairedWeyl r R hij • (e j : Vector r R) = e i := by
  funext k
  cases k with
  | inl k =>
    simp only [pairedWeyl, mul_smul, pairedTransvection_inl]
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [e, Pi.single_apply, hki, hkj, hij, Ne.symm hij]
  | inr k =>
    simp only [pairedWeyl, mul_smul, pairedTransvection_inr]
    simp [e, Pi.single_apply]

theorem pairedWeyl_f {i j : Fin r} (hij : i ≠ j) :
    pairedWeyl r R hij • (f j : Vector r R) = f i := by
  funext k
  cases k with
  | inl k =>
    simp only [pairedWeyl, mul_smul, pairedTransvection_inl]
    simp [f, Pi.single_apply]
  | inr k =>
    simp only [pairedWeyl, mul_smul, pairedTransvection_inr]
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [f, Pi.single_apply, hki, hkj, hij, Ne.symm hij]

theorem pairedTransvection_f_add {i j : Fin r} (hij : i ≠ j) :
    pairedTransvection r R hij (-1) • (f i : Vector r R) = f i + f j := by
  funext k
  cases k with
  | inl k => simp [pairedTransvection_inl, f, Pi.single_apply]
  | inr k =>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairedTransvection_inr, f, Pi.single_apply, hki, hkj, hij, Ne.symm hij]

end Atlas.Symplectic

import Atlas.LinearGroups.Orthogonal.OddSiegelCoordinates
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! The actual contragredient SL action on the odd quadratic space.
The last coordinate is fixed; no division by two or group order is used. -/
noncomputable section
namespace Atlas.Orthogonal
open Matrix
open scoped Matrix
variable (r : ℕ) (R : Type*) [CommRing R]

def oddDiagonalSLLinear (g : Matrix.SpecialLinearGroup (Fin r) R) :
    VectorB r R ≃ₗ[R] VectorB r R where
  toFun v := (Sum.elim (g.val *ᵥ (v.1 ∘ Sum.inl))
    ((g⁻¹).val.transpose *ᵥ (v.1 ∘ Sum.inr)), v.2)
  invFun v := (Sum.elim ((g⁻¹).val *ᵥ (v.1 ∘ Sum.inl))
    (g.val.transpose *ᵥ (v.1 ∘ Sum.inr)), v.2)
  left_inv v := by
    have hi : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
    apply Prod.ext
    · funext k
      cases k with
      | inl k =>
        change ((g⁻¹).val *ᵥ (g.val *ᵥ (v.1 ∘ Sum.inl))) k = _
        rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
        rfl
      | inr k =>
        change (g.val.transpose *ᵥ ((g⁻¹).val.transpose *ᵥ (v.1 ∘ Sum.inr))) k = _
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hi,
          Matrix.transpose_one, Matrix.one_mulVec]
        rfl
    · rfl
  right_inv v := by
    have hi : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
    apply Prod.ext
    · funext k
      cases k with
      | inl k =>
        change (g.val *ᵥ ((g⁻¹).val *ᵥ (v.1 ∘ Sum.inl))) k = _
        rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
        rfl
      | inr k =>
        change ((g⁻¹).val.transpose *ᵥ (g.val.transpose *ᵥ (v.1 ∘ Sum.inr))) k = _
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hi,
          Matrix.transpose_one, Matrix.one_mulVec]
        rfl
    · rfl
  map_add' v w := by
    apply Prod.ext
    · funext k
      cases k with
      | inl k =>
        change (g.val *ᵥ ((v.1 ∘ Sum.inl)+(w.1 ∘ Sum.inl))) k = _
        exact congrFun (Matrix.mulVec_add g.val (v.1 ∘ Sum.inl) (w.1 ∘ Sum.inl)) k
      | inr k =>
        change ((g⁻¹).val.transpose *ᵥ ((v.1 ∘ Sum.inr)+(w.1 ∘ Sum.inr))) k = _
        exact congrFun (Matrix.mulVec_add (g⁻¹).val.transpose (v.1 ∘ Sum.inr) (w.1 ∘ Sum.inr)) k
    · rfl
  map_smul' a v := by
    apply Prod.ext
    · funext k
      cases k with
      | inl k =>
        change (g.val *ᵥ (a • (v.1 ∘ Sum.inl))) k = _
        exact congrFun (Matrix.mulVec_smul g.val a (v.1 ∘ Sum.inl)) k
      | inr k =>
        change ((g⁻¹).val.transpose *ᵥ (a • (v.1 ∘ Sum.inr))) k = _
        exact congrFun (Matrix.mulVec_smul (g⁻¹).val.transpose a (v.1 ∘ Sum.inr)) k
    · rfl

@[simp] theorem oddDiagonalSLLinear_x (g : Matrix.SpecialLinearGroup (Fin r) R)
    (v : VectorB r R) (i : Fin r) :
    (oddDiagonalSLLinear r R g v).1 (.inl i) =
      (g.val *ᵥ (v.1 ∘ Sum.inl)) i := rfl

@[simp] theorem oddDiagonalSLLinear_y (g : Matrix.SpecialLinearGroup (Fin r) R)
    (v : VectorB r R) (i : Fin r) :
    (oddDiagonalSLLinear r R g v).1 (.inr i) =
      ((g⁻¹).val.transpose *ᵥ (v.1 ∘ Sum.inr)) i := rfl

@[simp] theorem oddDiagonalSLLinear_z (g : Matrix.SpecialLinearGroup (Fin r) R)
    (v : VectorB r R) : (oddDiagonalSLLinear r R g v).2 = v.2 := rfl

theorem oddDiagonalSLLinear_preserves (g : Matrix.SpecialLinearGroup (Fin r) R)
    (v : VectorB r R) : formB r R (oddDiagonalSLLinear r R g v) = formB r R v := by
  simp only [formB_apply, formD_apply, oddDiagonalSLLinear_x,
    oddDiagonalSLLinear_y, oddDiagonalSLLinear_z]
  change (g.val *ᵥ (v.1 ∘ Sum.inl)) ⬝ᵥ
    ((g⁻¹).val.transpose *ᵥ (v.1 ∘ Sum.inr)) + v.2^2 =
      (v.1 ∘ Sum.inl) ⬝ᵥ (v.1 ∘ Sum.inr) + v.2^2
  have hi : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hi,
    Matrix.one_mulVec, dotProduct_comm]

/-- A literal SL subgroup of the established odd quadratic group. -/
def oddDiagonalSLHom : Matrix.SpecialLinearGroup (Fin r) R →* O_B r R where
  toFun g := ⟨oddDiagonalSLLinear r R g, oddDiagonalSLLinear_preserves r R g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply Prod.ext
    · funext k
      cases k <;> simp [oddDiagonalSLLinear]
    · rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply Prod.ext
    · funext k
      cases k with
      | inl k =>
        change ((g*h).val *ᵥ (v.1 ∘ Sum.inl)) k =
          (g.val *ᵥ (h.val *ᵥ (v.1 ∘ Sum.inl))) k
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
      | inr k =>
        change (((g*h)⁻¹).val.transpose *ᵥ (v.1 ∘ Sum.inr)) k =
          ((g⁻¹).val.transpose *ᵥ ((h⁻¹).val.transpose *ᵥ (v.1 ∘ Sum.inr))) k
        rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
          Matrix.mulVec_mulVec]
    · rfl

/-- The mixed-long Siegel family is the literal elementary SL block. -/
theorem oddDiagonalSLHom_transvection (F : Type*) [Field F]
    (i j : Fin r) (hij : i ≠ j) (t : F) :
    oddDiagonalSLHom r F (Matrix.SpecialLinearGroup.transvection hij t) =
      oddLong r F i j hij t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · funext k
    cases k with
    | inl k =>
      change (Matrix.transvection i j t *ᵥ (v.1 ∘ Sum.inl)) k = _
      simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec_eq,
        Pi.single_apply, eq_comm]
    | inr k =>
      change (((Matrix.SpecialLinearGroup.transvection hij t)⁻¹).val.transpose *ᵥ
        (v.1 ∘ Sum.inr)) k = _
      rw [Matrix.SpecialLinearGroup.transvection_inv]
      simp [
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
        Matrix.add_mulVec, Matrix.single_mulVec_eq, Pi.single_apply, sub_eq_add_neg, eq_comm]
  · change v.2 = ((oddLong r F i j hij t).val v).2
    rw [oddLong_apply_z]

end Atlas.Orthogonal

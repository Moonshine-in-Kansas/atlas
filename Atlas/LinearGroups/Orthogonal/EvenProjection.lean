import Atlas.LinearGroups.Orthogonal.Transitivity
import Atlas.LinearGroups.Symplectic.Isometry
import Mathlib.Algebra.CharP.Two

/-! # The actual characteristic-two B action on its polar quotient -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F] [CharP F 2]

theorem polarD_eq_symplectic (x y : VectorD n F) :
    (formD n F).polarBilin x y = Atlas.Symplectic.form x y := by
  rw [polarD_apply, Atlas.Symplectic.form_apply]
  simp only [CharTwo.sub_eq_add]
  congr 1
  funext i
  ring

/-- Every full quadratic isometry fixes the distinguished radical vector itself. -/
theorem even_fix_z (g : O_B n F) : g.val z = z := by
  have hp : ∀ w, (formB n F).polarBilin (g.val z) w = 0 := by
    intro w
    have h := Atlas.Quadratic.isometry_polar (formB n F)
      (isometryCarrierEquiv _ g) z (g.val.symm w)
    change (formB n F).polarBilin (g.val z) (g.val (g.val.symm w)) = _ at h
    rw [g.val.apply_symm_apply] at h
    rw [h]
    simp only [polarB_apply, z, map_zero, LinearMap.zero_apply, CharTwo.two_eq_zero,
      zero_mul, add_zero]
  obtain ⟨a, ha⟩ := (polarB_radical_charTwo CharTwo.two_eq_zero (g.val z)).mp hp
  have hs : a ^ 2 = 1 := by
    have h := g.prop z
    rw [ha, (formB n F).map_smul, formB_z] at h
    simpa only [smul_eq_mul, mul_one, pow_two] using h
  have hone : a = 1 := by
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  simpa only [hone, one_smul] using ha

theorem even_first (g : O_B n F) (x : VectorB n F) :
    (g.val x).1 = (g.val (x.1, 0)).1 := by
  have hx : x = (x.1, 0) + x.2 • z := by ext <;> simp [z]
  calc
    (g.val x).1 = (g.val ((x.1, 0) + x.2 • z)).1 := congrArg (fun t => (g.val t).1) hx
    _ = (g.val (x.1, 0)).1 := by rw [map_add, map_smul, even_fix_z]; simp [z]

def evenProjectionLinear (g : O_B n F) : VectorD n F ≃ₗ[F] VectorD n F where
  toFun x := (g.val (x, 0)).1
  invFun x := ((g⁻¹).val (x, 0)).1
  left_inv x := by
    dsimp only
    rw [← even_first (g⁻¹) (g.val (x, 0))]
    change (g.val.symm (g.val (x, 0))).1 = x
    rw [g.val.symm_apply_apply]
  right_inv x := by
    dsimp only
    rw [← even_first g ((g⁻¹).val (x, 0))]
    change (g.val (g.val.symm (x, 0))).1 = x
    rw [g.val.apply_symm_apply]
  map_add' x y := by
    simpa using
      congrArg Prod.fst (map_add g.val (x, 0) (y, 0))
  map_smul' a x := by
    simpa using
      congrArg Prod.fst (map_smul g.val a (x, 0))

theorem evenProjection_preserves (g : O_B n F) (x y : VectorD n F) :
    Atlas.Symplectic.form (evenProjectionLinear g x) (evenProjectionLinear g y) =
      Atlas.Symplectic.form x y := by
  have h := Atlas.Quadratic.isometry_polar (formB n F) (isometryCarrierEquiv _ g) (x, 0) (y, 0)
  simp only [polarB_apply, CharTwo.two_eq_zero, zero_mul, add_zero, polarD_eq_symplectic] at h
  exact h

/-- Projection is a homomorphism into the existing primary symplectic matrix model. -/
def evenProjection : O_B n F →* Atlas.Symplectic.Sp n F where
  toFun g := Atlas.Symplectic.ofLinear (evenProjectionLinear g) (evenProjection_preserves g)
  map_one' := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Atlas.Symplectic.Vector n F)
    intro x
    rw [Atlas.Symplectic.ofLinear_apply, one_smul]
    rfl
  map_mul' g h := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Atlas.Symplectic.Vector n F)
    intro x
    rw [mul_smul, Atlas.Symplectic.ofLinear_apply, Atlas.Symplectic.ofLinear_apply,
      Atlas.Symplectic.ofLinear_apply]
    change (g.val (h.val (x, 0))).1 = (g.val ((h.val (x, 0)).1, 0)).1
    exact even_first g (h.val (x, 0))

end Atlas.Orthogonal

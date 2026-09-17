import Atlas.LinearGroups.Symplectic.ProjectiveInvolutionLift
import Atlas.LinearGroups.Symplectic.Isometry
import Atlas.LinearAlgebra.SymplecticInvolutionConjugacy
import Atlas.LinearAlgebra.SymplecticSquareMinusOneConjugacy

noncomputable section


namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

def minusDimension (g : Sp n F) : ℕ :=
  Module.finrank F (Atlas.LinearInvolution.minus (toLinear g).toLinearMap)

theorem isConj_of_linear_intertwiner (g h : Sp n F)
    (a : Vector n F ≃ₗ[F] Vector n F)
    (ha : ∀ x y, form (a x) (a y) = form x y)
    (hat : ∀ x, a (g • x) = h • a x) : IsConj g h := by
  rw [isConj_iff]
  refine ⟨ofLinear a ha,?_⟩
  apply ext_action
  intro x
  have he (y : Vector n F) : (ofLinear a ha)⁻¹ • y = a.symm y := by
    apply a.injective
    rw [←ofLinear_apply a ha]
    simp
  simpa only [mul_smul,ofLinear_apply,he,LinearEquiv.apply_symm_apply] using
    hat (a.symm x)

theorem square_one_isConj_of_minusDimension_eq (g h : Sp n F)
    (hg : g^2 = 1) (hh : h^2 = 1) (h2 : (2 : F) ≠ 0)
    (hd : minusDimension g = minusDimension h) : IsConj g h := by
  have hg' : Function.Involutive (toLinear g).toLinearMap := by
    intro x
    change g • (g • x) = x
    rw [←mul_smul,←pow_two,hg,one_smul]
  have hh' : Function.Involutive (toLinear h).toLinearMap := by
    intro x
    change h • (h • x) = x
    rw [←mul_smul,←pow_two,hh,one_smul]
  obtain ⟨a,ha,hat⟩ := Atlas.AlternatingForm.involution_isometry_exists
    form form_alternating form_nondegenerate form form_alternating form_nondegenerate
    (toLinear g).toLinearMap (toLinear h).toLinearMap hg' hh' (preserves g) (preserves h)
    h2 rfl hd
  exact isConj_of_linear_intertwiner g h a ha hat

theorem square_negativeIdentity_isConj [Finite F] (g h : Sp n F)
    (hg : g^2 = negativeIdentity) (hh : h^2 = negativeIdentity) (h2 : (2 : F) ≠ 0) :
    IsConj g h := by
  have hg' : ∀ x, (toLinear g) ((toLinear g) x) = -x := by
    intro x
    change g • (g • x) = -x
    rw [←mul_smul,←pow_two,hg,negativeIdentity_apply]
  have hh' : ∀ x, (toLinear h) ((toLinear h) x) = -x := by
    intro x
    change h • (h • x) = -x
    rw [←mul_smul,←pow_two,hh,negativeIdentity_apply]
  obtain ⟨a,ha,hat⟩ := Atlas.AlternatingForm.squareMinusOne_isometry_exists
    form form_alternating (toLinear g).toLinearMap hg' (preserves g) form_nondegenerate
    form form_alternating form_nondegenerate (toLinear h).toLinearMap hh' (preserves h) h2 rfl
  exact isConj_of_linear_intertwiner g h a ha hat

end Atlas.Symplectic

namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]
open Atlas.LinearInvolution

def minusEquivOfIntertwiner (g h : Sp n F) (a : Vector n F ≃ₗ[F] Vector n F)
    (hat : ∀ x, a (g • x) = h • a x) :
    minus (toLinear g).toLinearMap ≃ₗ[F] minus (toLinear h).toLinearMap where
  toFun x := ⟨a x.val,by
    rw [mem_minus]
    change h • a x.val = -a x.val
    rw [←hat]
    have hx : g • x.val = -x.val := (mem_minus _ _).mp x.prop
    rw [hx,map_neg]⟩
  invFun x := ⟨a.symm x.val,by
    rw [mem_minus]
    apply a.injective
    change a (g • a.symm x.val) = a (-a.symm x.val)
    rw [hat,map_neg,LinearEquiv.apply_symm_apply]
    exact (mem_minus _ _).mp x.prop⟩
  left_inv x := by apply Subtype.ext; exact a.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact a.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact a.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact a.map_smul c x.val

theorem minusDimension_eq_of_isConj (g h : Sp n F) (hc : IsConj g h) :
    minusDimension g = minusDimension h := by
  obtain ⟨a,ha⟩ := isConj_iff.mp hc
  apply LinearEquiv.finrank_eq (minusEquivOfIntertwiner g h (toLinear a) ?_)
  intro x
  change a • (g • x) = h • (a • x)
  rw [←ha,mul_smul,mul_smul,inv_smul_smul]

theorem square_one_isConj_iff_minusDimension_eq (g h : Sp n F)
    (hg : g^2=1) (hh : h^2=1) (h2 : (2:F) ≠ 0) :
    IsConj g h ↔ minusDimension g = minusDimension h :=
  ⟨minusDimension_eq_of_isConj g h,square_one_isConj_of_minusDimension_eq g h hg hh h2⟩

end Atlas.Symplectic

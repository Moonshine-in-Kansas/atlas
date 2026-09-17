import Atlas.LinearAlgebra.QuadraticInvolutionClass

noncomputable section
namespace Atlas.Quadratic
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F V) (R : QuadraticForm F W)

def conjugateIsometry (e : Q.IsometryEquiv R) (g : Q.IsometryEquiv Q) : R.IsometryEquiv R :=
  e.symm.trans (g.trans e)

theorem conjugateIsometry_involutive (e : Q.IsometryEquiv R) (g : Q.IsometryEquiv Q)
    (hg : Function.Involutive g) : Function.Involutive (conjugateIsometry Q R e g) := by
  intro x
  change e (g (e.symm (e (g (e.symm x))))) = x
  rw [e.symm_apply_apply,hg,e.apply_symm_apply]

def conjugateMinusIsometry (e : Q.IsometryEquiv R) (g : Q.IsometryEquiv Q) :
    (Q.comp (Atlas.LinearInvolution.minus g.toLinearEquiv.toLinearMap).subtype).IsometryEquiv
      (R.comp (Atlas.LinearInvolution.minus
        (conjugateIsometry Q R e g).toLinearEquiv.toLinearMap).subtype) where
  toLinearEquiv := {
    toFun := fun x => ⟨e x.val,by
      rw [Atlas.LinearInvolution.mem_minus]
      change e (g (e.symm (e x.val))) = -e x.val
      rw [e.symm_apply_apply]
      have hx := (Atlas.LinearInvolution.mem_minus _ _).mp x.prop
      change g x.val = -x.val at hx
      rw [hx,map_neg]⟩
    invFun := fun x => ⟨e.symm x.val,by
      rw [Atlas.LinearInvolution.mem_minus]
      apply e.injective
      change e (g (e.symm x.val)) = e (-e.symm x.val)
      rw [map_neg,e.apply_symm_apply]
      exact (Atlas.LinearInvolution.mem_minus _ _).mp x.prop⟩
    left_inv := fun x => by apply Subtype.ext; exact e.symm_apply_apply x.val
    right_inv := fun x => by apply Subtype.ext; exact e.apply_symm_apply x.val
    map_add' := fun x y => by apply Subtype.ext; exact e.toLinearEquiv.map_add x.val y.val
    map_smul' := fun c x => by apply Subtype.ext; exact e.toLinearEquiv.map_smul c x.val }
  map_app' x := e.map_app x.val

theorem conjugateIsometry_finrank_minus [FiniteDimensional F V] [FiniteDimensional F W]
    (e : Q.IsometryEquiv R) (g : Q.IsometryEquiv Q) :
    Module.finrank F (Atlas.LinearInvolution.minus (conjugateIsometry Q R e g).toLinearEquiv.toLinearMap) =
      Module.finrank F (Atlas.LinearInvolution.minus g.toLinearEquiv.toLinearMap) :=
  (conjugateMinusIsometry Q R e g).toLinearEquiv.finrank_eq.symm
end Atlas.Quadratic

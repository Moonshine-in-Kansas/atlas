import Mathlib.Algebra.Module.Equiv.Basic

namespace Atlas.LinearAlgebra

/-- Transport of the full linear automorphism group along a linear equivalence. -/
def linearAutomorphismCongr
    {R V W : Type*} [Semiring R] [AddCommMonoid V] [AddCommMonoid W]
    [Module R V] [Module R W] (e : V ≃ₗ[R] W) :
    (V ≃ₗ[R] V) ≃* (W ≃ₗ[R] W) where
  toFun f := e.symm.trans (f.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv f := by
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
  right_inv g := by
    apply LinearEquiv.ext
    intro w
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
  map_mul' f g := by
    apply LinearEquiv.ext
    intro w
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

@[simp] theorem linearAutomorphismCongr_apply
    {R V W : Type*} [Semiring R] [AddCommMonoid V] [AddCommMonoid W]
    [Module R V] [Module R W] (e : V ≃ₗ[R] W) (f : V ≃ₗ[R] V) (w : W) :
    linearAutomorphismCongr e f w = e (f (e.symm w)) := rfl

@[simp] theorem linearAutomorphismCongr_symm_apply
    {R V W : Type*} [Semiring R] [AddCommMonoid V] [AddCommMonoid W]
    [Module R V] [Module R W] (e : V ≃ₗ[R] W) (g : W ≃ₗ[R] W) (v : V) :
    (linearAutomorphismCongr e).symm g v = e.symm (g (e v)) := rfl

end Atlas.LinearAlgebra

import Atlas.LinearGroups.Orthogonal.IsometryTransport
import Atlas.LinearAlgebra.QuadraticResidual
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.ZMod.Basic

/-! # Intrinsic residual-rank parity on the actual orthogonal carrier

This defines the proposed Dickson invariant as a function. Multiplicativity and
identification of its kernel are separate obligations, not assumptions here.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F V)

def dicksonValue (g : isometrySubgroup Q) : ZMod 2 :=
  (Module.finrank F (residual Q (isometryCarrierEquiv Q g)) : ZMod 2)

@[simp] theorem dicksonValue_one : dicksonValue Q 1 = 0 := by
  have hz : residual Q (isometryCarrierEquiv Q 1) = ⊥ := by
    apply le_antisymm _ bot_le
    rintro x ⟨y, hy⟩
    change y - y = x at hy
    simpa only [sub_self, Submodule.mem_bot] using hy.symm
  change (Module.finrank F (residual Q (isometryCarrierEquiv Q 1)) : ZMod 2) = 0
  rw [hz, finrank_bot, Nat.cast_zero]

theorem residual_inverse (g : isometrySubgroup Q) :
    residual Q (isometryCarrierEquiv Q g⁻¹) = residual Q (isometryCarrierEquiv Q g) := by
  apply le_antisymm
  · rintro x ⟨y, hy⟩
    refine ⟨-(g.val.symm y), ?_⟩
    change -(g.val.symm y) - g.val (-(g.val.symm y)) = x
    change y - g.val.symm y = x at hy
    rw [map_neg, g.val.apply_symm_apply]
    convert hy using 1 <;> abel
  · rintro x ⟨y, hy⟩
    refine ⟨-(g.val y), ?_⟩
    change -(g.val y) - g.val.symm (-(g.val y)) = x
    change y - g.val y = x at hy
    rw [map_neg, g.val.symm_apply_apply]
    convert hy using 1 <;> abel

@[simp] theorem dicksonValue_inv (g : isometrySubgroup Q) :
    dicksonValue Q g⁻¹ = dicksonValue Q g := by
  exact congrArg (fun S : Submodule F V => (Module.finrank F S : ZMod 2))
    (residual_inverse Q g)

theorem residual_isometry_transport {R : QuadraticForm F W}
    (i : Q.IsometryEquiv R) (g : isometrySubgroup Q) :
    residual R (isometryCarrierEquiv R (isometryGroupTransport i g)) =
      (residual Q (isometryCarrierEquiv Q g)).map i.toLinearEquiv.toLinearMap := by
  apply le_antisymm
  · rintro x ⟨y, hy⟩
    refine ⟨i.symm y - g.val (i.symm y), ⟨i.symm y, rfl⟩, ?_⟩
    change y - i (g.val (i.symm y)) = x at hy
    change i (i.symm y - g.val (i.symm y)) = x
    rw [map_sub, i.apply_symm_apply]
    exact hy
  · rintro x ⟨u, ⟨y, hy⟩, hx⟩
    refine ⟨i y, ?_⟩
    change i y - i (g.val (i.symm (i y))) = x
    change y - g.val y = u at hy
    rw [i.symm_apply_apply, ← map_sub, hy]
    exact hx

theorem dicksonValue_isometry_transport {R : QuadraticForm F W}
    (i : Q.IsometryEquiv R) (g : isometrySubgroup Q) :
    dicksonValue R (isometryGroupTransport i g) = dicksonValue Q g := by
  change (Module.finrank F (residual R (isometryCarrierEquiv R (isometryGroupTransport i g))) : ZMod 2) = _
  rw [residual_isometry_transport, LinearEquiv.finrank_map_eq]
  rfl
end Atlas.Orthogonal

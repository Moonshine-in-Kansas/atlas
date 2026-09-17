import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace Atlas.LinearFunctional
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Translation by a normalized section identifies each affine fibre with the kernel. -/
def fiberEquivKernel (l : V →ₗ[F] F) (v : V) (hv : l v = 1) (c : F) :
    {x : V // l x = c} ≃ l.ker where
  toFun x := ⟨x.val-c • v, by simp [map_sub,map_smul,x.prop,hv]⟩
  invFun x := ⟨x.val+c • v, by simp [map_add,map_smul,x.prop,hv]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem card_fiber [Finite F] [FiniteDimensional F V]
    (l : V →ₗ[F] F) (v : V) (hv : l v = 1) (c : F) :
    Nat.card {x : V // l x = c} = Nat.card F ^ (Module.finrank F V - 1) := by
  have hr : LinearMap.range l = ⊤ := LinearMap.range_eq_top.mpr (by
    intro a
    exact ⟨a • v,by simp [map_smul,hv]⟩)
  have hk := l.finrank_range_add_finrank_ker
  rw [hr,finrank_top,Module.finrank_self] at hk
  have hd : Module.finrank F l.ker = Module.finrank F V - 1 := by omega
  rw [Nat.card_congr (fiberEquivKernel l v hv c),Module.natCard_eq_pow_finrank (K := F),hd]
end Atlas.LinearFunctional

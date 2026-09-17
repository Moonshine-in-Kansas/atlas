import Atlas.LinearAlgebra.InvolutionEigenspaces
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Nondegenerate restrictions to the two eigenspaces -/
noncomputable section
namespace Atlas.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private theorem restriction_nondegenerate (b : LinearMap.BilinForm F V)
    (hn : b.Nondegenerate) (P R : Submodule F V) (hc : IsCompl P R)
    (hpr : ∀ x : P, ∀ y : R, b x.val y.val = 0)
    (hrp : ∀ y : R, ∀ x : P, b y.val x.val = 0) :
    (b.restrict P).Nondegenerate := by
  let e := Submodule.prodEquivOfIsCompl P R hc
  constructor
  · intro x hx
    apply Subtype.ext
    apply hn.1 x.val
    intro z
    obtain ⟨⟨p,r⟩,rfl⟩ := e.surjective z
    change b x.val (p.val + r.val) = 0
    rw [map_add,hpr x r,add_zero]
    exact hx p
  · intro x hx
    apply Subtype.ext
    apply hn.2 x.val
    intro z
    obtain ⟨⟨p,r⟩,rfl⟩ := e.surjective z
    change b (p.val + r.val) x.val = 0
    rw [map_add,LinearMap.add_apply,hrp r x,add_zero]
    exact hx p

theorem plus_nondegenerate (b : LinearMap.BilinForm F V) (hn : b.Nondegenerate)
    (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (hb : ∀ x y, b (t x) (t y) = b x y) (h2 : (2 : F) ≠ 0) :
    (b.restrict (plus t)).Nondegenerate :=
  restriction_nondegenerate b hn _ _ (isCompl t ht h2)
    (orthogonal b t hb h2) (fun y x => orthogonal b.flip t (fun x y => hb y x) h2 x y)

theorem minus_nondegenerate (b : LinearMap.BilinForm F V) (hn : b.Nondegenerate)
    (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (hb : ∀ x y, b (t x) (t y) = b x y) (h2 : (2 : F) ≠ 0) :
    (b.restrict (minus t)).Nondegenerate :=
  restriction_nondegenerate b hn _ _ (isCompl t ht h2).symm
    (fun y x => orthogonal b.flip t (fun x y => hb y x) h2 x y) (orthogonal b t hb h2)

theorem finrank_plus_add_minus [FiniteDimensional F V] (t : V →ₗ[F] V)
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    Module.finrank F (plus t) + Module.finrank F (minus t) = Module.finrank F V := by
  rw [← Module.finrank_prod]
  exact (decomposition t ht h2).finrank_eq
end Atlas.LinearInvolution

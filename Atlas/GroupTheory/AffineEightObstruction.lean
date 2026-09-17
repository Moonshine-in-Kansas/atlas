import Atlas.GroupTheory.SixteenEightObstruction
import Mathlib.GroupTheory.SemidirectProduct

noncomputable section
namespace Atlas.GroupTheory
open MulAction SemidirectProduct

def fixedByConjugateEquiv {G X : Type*} [Group G] [MulAction G X] (g u : G) :
    fixedBy X u ≃ fixedBy X (g*u*g⁻¹) where
  toFun x := ⟨g • x.val,by
    change (g*u*g⁻¹) • (g • x.val) = g • x.val
    simp [mul_smul,show u • x.val = x.val from x.prop]⟩
  invFun x := ⟨g⁻¹ • x.val,by
    have h := congrArg (fun y : X => g⁻¹ • y) x.prop
    simpa [mul_smul] using h⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem affine_no_faithful_eight {U B X : Type*} [Group U] [Group B]
    [Finite U] [Finite X] (φ : B →* MulAut U)
    [MulAction (U ⋊[φ] B) X] [FaithfulSMul (U ⋊[φ] B) X]
    (hu : Nat.card U = 16) (hx : Nat.card X = 8)
    (transitive : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃ b, φ b u = v) : False := by
  haveI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v,hv⟩ := exists_ne (1 : U)
  letI : MulAction U X := MulAction.compHom X (inl : U →* U ⋊[φ] B)
  have uniform (u : U) (hun : u ≠ 1) :
      Nat.card (fixedBy X u) = Nat.card (fixedBy X v) := by
    obtain ⟨b,hb⟩ := transitive v u hv hun
    have he : (inr b : U ⋊[φ] B) * inl v * (inr b)⁻¹ = inl u := by
      rw [← map_inv,← inl_aut,hb]
    have h := Nat.card_congr (fixedByConjugateEquiv (X := X)
      (inr b : U ⋊[φ] B) (inl v))
    rw [he] at h
    exact h.symm
  have htriv := sixteen_eight_fixed hu hx (Nat.card (fixedBy X v)) uniform
  have he : (inl v : U ⋊[φ] B) = 1 := by
    apply eq_of_smul_eq_smul (α := X)
    intro x
    exact (htriv v x).trans (one_smul (U ⋊[φ] B) x).symm
  exact hv (inl_injective (he.trans (map_one inl).symm))

end Atlas.GroupTheory

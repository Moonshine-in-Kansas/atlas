import Mathlib.GroupTheory.GroupAction.Primitive

namespace Atlas.GroupTheory
open MulAction

/-- An equivariant map from a primitive action is injective or constant. -/
theorem primitive_map_injective_or_constant {G H A X : Type*}
    [Group G] [Group H] [MulAction G A] [MulAction H X] [IsPreprimitive G A]
    {φ : G → H} (f : A →ₑ[φ] X) :
    Function.Injective f ∨ ∀ a b, f a = f b := by
  classical
  by_cases hi : Function.Injective f
  · exact Or.inl hi
  right
  obtain ⟨a,b,hab,hne⟩ := Function.not_injective_iff.mp hi
  have hB : IsBlock G (f ⁻¹' {f a}) := IsBlock.preimage f (IsBlock.singleton)
  rcases hB.subsingleton_or_eq_univ with hs | hu
  · exact False.elim (hne (hs (by simp) (by simpa using hab.symm)))
  · intro c d
    have hc : c ∈ f ⁻¹' {f a} := by rw [hu]; trivial
    have hd : d ∈ f ⁻¹' {f a} := by rw [hu]; trivial
    exact hc.trans hd.symm

end Atlas.GroupTheory

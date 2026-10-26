import Mathlib.Algebra.Group.Action.Pretransitive

namespace Atlas.GroupTheory

/-- Transitivity on the complement of a point, together with an element moving
that point, implies transitivity on the whole action. -/
theorem isPretransitive_of_complement_transitive {G X : Type*} [Group G] [MulAction G X]
    (a : X) (hcomp : ∀x y : X,x≠a → y≠a → ∃g : G,g • x=y)
    (hmove : ∃g : G,g • a≠a) : MulAction.IsPretransitive G X := by
  classical
  obtain ⟨g,hg⟩ := hmove
  have hr (x : X) : ∃h : G,h • a=x := by
    by_cases hx : x=a
    · exact ⟨1,by simpa only [one_smul] using hx.symm⟩
    · obtain ⟨h,hh⟩ := hcomp (g • a) x hg hx
      exact ⟨h*g,by rw [mul_smul,hh]⟩
  constructor
  intro x y
  obtain ⟨g,hg⟩ := hr x
  obtain ⟨h,hh⟩ := hr y
  exact ⟨h*g⁻¹,by rw [mul_smul,←hg,inv_smul_smul,hh]⟩

end Atlas.GroupTheory

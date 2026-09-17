import Mathlib.Data.Fintype.BigOperators

namespace Atlas.Algebra

/-- Additive dependent splitting over a finite type. -/
theorem fintype_sum_dite {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    {p : ι → Prop} [DecidablePred p]
    (f : ∀ i, p i → A) (g : ∀ i, ¬p i → A) :
    (∑ i, dite (p i) (f i) (g i)) =
      (∑ i : {i // p i}, f i i.property) + ∑ i : {i // ¬p i}, g i i.property := by
  simp only [Finset.sum_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).sum_comp fun i : {i // p i} => f i i.property
  · exact (Equiv.subtypeEquivRight <| by simp).sum_comp fun i : {i // ¬p i} => g i i.property

end Atlas.Algebra

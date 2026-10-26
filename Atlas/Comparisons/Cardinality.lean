import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace Atlas.Comparisons

/-- A group isomorphism preserves cardinality; unequal finite orders therefore
exclude any multiplicative equivalence. The statement also holds with Nat.card
for arbitrary group types. -/
theorem not_isomorphic_of_card_ne {G : Type*} {H : Type*} [Group G] [Group H]
    (h : Nat.card G ≠ Nat.card H) : ¬ Nonempty (G ≃* H) := by
  rintro ⟨e⟩
  exact h (Nat.card_congr e.toEquiv)

end Atlas.Comparisons

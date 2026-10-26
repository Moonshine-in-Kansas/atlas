import Atlas.Families.Alternating.Basic

open scoped BigOperators
universe u v

theorem AtlasExistence.alternating (n : ℕ) (hn : 5 ≤ n) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = n.factorial / 2 ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Families.Alternating.Model n, inferInstance, inferInstance,
    Atlas.Families.Alternating.card_factorial n (by omega),
    Atlas.Families.Alternating.isSimpleGroup n hn⟩


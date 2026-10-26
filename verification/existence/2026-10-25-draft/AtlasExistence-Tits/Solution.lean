import Atlas.Tits.Construction

open scoped BigOperators
universe u v

theorem AtlasExistence.Tits :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 17971200 ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Tits.Model,inferInstance,Atlas.Tits.finite,Atlas.Tits.card,
    Atlas.Tits.isSimpleGroup⟩

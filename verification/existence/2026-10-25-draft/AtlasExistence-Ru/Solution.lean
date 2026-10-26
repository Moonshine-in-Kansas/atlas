import Atlas.Sporadic.Rudvalis

open scoped BigOperators
universe u v

theorem AtlasExistence.Ru :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 145926144000 ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Sporadic.Rudvalis.Model,inferInstance,Atlas.Sporadic.Rudvalis.finite,
    Atlas.Sporadic.Rudvalis.card,Atlas.Sporadic.Rudvalis.isSimpleGroup⟩


import Atlas.Sporadic.Mathieu24Construction

open scoped BigOperators
universe u v

theorem AtlasExistence.M24  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 244823040 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu24.Model , inferInstance, Atlas.Sporadic.Mathieu24.finite ,
      Atlas.Sporadic.Mathieu24.card , Atlas.Sporadic.Mathieu24.isSimpleGroup ⟩


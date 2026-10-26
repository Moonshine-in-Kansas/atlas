import Atlas.Sporadic.McLaughlinConstruction

open scoped BigOperators
universe u v

theorem AtlasExistence.McL  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 898128000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.McLaughlin.Model , inferInstance, Atlas.Sporadic.McLaughlin.finite ,
      Atlas.Sporadic.McLaughlin.card , Atlas.Sporadic.McLaughlin.isSimpleGroup ⟩


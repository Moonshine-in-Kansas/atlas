import Atlas.Sporadic.SuzukiConstruction

open scoped BigOperators
universe u v

theorem AtlasExistence.Suz  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 448345497600 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Suzuki.Model , inferInstance, Atlas.Sporadic.Suzuki.finite ,
      Atlas.Sporadic.Suzuki.card , Atlas.Sporadic.Suzuki.isSimpleGroup ⟩


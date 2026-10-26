import Atlas.Sporadic.Fischer23

open scoped BigOperators
universe u v

theorem AtlasExistence.Fi23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4089470473293004800 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Fischer23.Model , inferInstance, Atlas.Sporadic.Fischer23.finite ,
      Atlas.Sporadic.Fischer23.card , Atlas.Sporadic.Fischer23.simple ⟩


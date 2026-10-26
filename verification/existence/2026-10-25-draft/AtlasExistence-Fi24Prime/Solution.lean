import Atlas.Sporadic.Fischer24Prime

open scoped BigOperators
universe u v

theorem AtlasExistence.Fi24Prime  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 1255205709190661721292800 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Fischer24Prime.Model , inferInstance, Atlas.Sporadic.Fischer24Prime.finite ,
      Atlas.Sporadic.Fischer24Prime.card , Atlas.Sporadic.Fischer24Prime.simple ⟩



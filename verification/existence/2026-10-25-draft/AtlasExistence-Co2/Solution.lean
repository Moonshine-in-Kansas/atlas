import Atlas.Sporadic.Conway2Construction

open scoped BigOperators
universe u v

theorem AtlasExistence.Co2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 42305421312000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Conway2.Model , inferInstance, Atlas.Sporadic.Conway2.finite ,
      Atlas.Sporadic.Conway2.card , Atlas.Sporadic.Conway2.isSimpleGroup ⟩


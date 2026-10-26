import Atlas.Sporadic.Conway3Construction

open scoped BigOperators
universe u v

theorem AtlasExistence.Co3  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 495766656000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Conway3.Model , inferInstance, Atlas.Sporadic.Conway3.finite ,
      Atlas.Sporadic.Conway3.card , Atlas.Sporadic.Conway3.isSimpleGroup ⟩


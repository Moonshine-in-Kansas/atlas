import Atlas.Sporadic.Conway1

open scoped BigOperators
universe u v

theorem AtlasExistence.Co1  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4157776806543360000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Conway1.Model , inferInstance, Atlas.Sporadic.Conway1.finite ,
      Atlas.Sporadic.Conway1.card , Atlas.Sporadic.Conway1.isSimpleGroup ⟩


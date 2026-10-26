import Atlas.Sporadic.Janko2Construction

open scoped BigOperators
universe u v

theorem AtlasExistence.J2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 604800 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Janko2.Model , inferInstance, Atlas.Sporadic.Janko2.finite ,
      Atlas.Sporadic.Janko2.card , Atlas.Sporadic.Janko2.isSimpleGroup ⟩


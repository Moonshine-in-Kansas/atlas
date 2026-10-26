import Atlas.Sporadic.Mathieu23

open scoped BigOperators
universe u v

theorem AtlasExistence.M23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 10200960 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu23.Model ((0,0),0), inferInstance, Atlas.Sporadic.Mathieu23.finite ((0,0),0),
      Atlas.Sporadic.Mathieu23.card ((0,0),0), Atlas.Sporadic.Mathieu23.isSimpleGroup ((0,0),0)⟩


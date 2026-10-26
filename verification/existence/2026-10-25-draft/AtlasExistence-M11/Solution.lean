import Atlas.Sporadic.Mathieu11

open scoped BigOperators
universe u v

theorem AtlasExistence.M11  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 7920 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu11.Model Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint, inferInstance, Atlas.Sporadic.Mathieu11.finite Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint,
      Atlas.Sporadic.Mathieu11.card Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint, Atlas.Sporadic.Mathieu11.isSimpleGroup Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint⟩


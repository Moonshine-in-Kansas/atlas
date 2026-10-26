import Atlas.Sporadic.Mathieu12

open scoped BigOperators
universe u v

theorem AtlasExistence.M12  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 95040 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu12.Model Atlas.Sporadic.Mathieu12.standardDodecad, inferInstance, Atlas.Sporadic.Mathieu12.finite Atlas.Sporadic.Mathieu12.standardDodecad,
      Atlas.Sporadic.Mathieu12.card Atlas.Sporadic.Mathieu12.standardDodecad, Atlas.Sporadic.Mathieu12.isSimpleGroup Atlas.Sporadic.Mathieu12.standardDodecad⟩


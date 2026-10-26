import Atlas.Sporadic.Mathieu22Simple

open scoped BigOperators
universe u v

theorem AtlasExistence.M22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 443520 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Mathieu22.Model ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩, inferInstance, Atlas.Sporadic.Mathieu22.finite ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩,
      Atlas.Sporadic.Mathieu22.card ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩, Atlas.Sporadic.Mathieu22.isSimpleGroup ((0,0),0) ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩⟩


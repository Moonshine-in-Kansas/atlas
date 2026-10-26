import Atlas.Sporadic.Fischer22

open scoped BigOperators
universe u v

theorem AtlasExistence.Fi22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 64561751654400 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.Fischer22.Model , inferInstance, Atlas.Sporadic.Fischer22.finite ,
      Atlas.Sporadic.Fischer22.card , Atlas.Sporadic.Fischer22.simple ⟩


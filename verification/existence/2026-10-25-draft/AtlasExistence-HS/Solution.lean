import Atlas.Sporadic.HigmanSimsConstruction

open scoped BigOperators
universe u v

theorem AtlasExistence.HS  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 44352000 ∧ IsSimpleGroup G := by
    exact ⟨Atlas.Sporadic.HigmanSims.Model , inferInstance, Atlas.Sporadic.HigmanSims.finite ,
      Atlas.Sporadic.HigmanSims.card , Atlas.Sporadic.HigmanSims.isSimpleGroup ⟩


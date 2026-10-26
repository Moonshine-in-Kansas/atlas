import Atlas.LinearGroups.TypeF4

open scoped BigOperators
universe u v

theorem AtlasExistence.F4 {F : Type u} [Field F] [Finite F] :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F^24*(Nat.card F^12-1)*(Nat.card F^8-1)*
      (Nat.card F^6-1)*(Nat.card F^2-1) ∧ IsSimpleGroup G := by
  have h := Atlas.typeF4_construction (F := F)
  exact ⟨Atlas.F4.Model F,inferInstance,h.finite,h.order,h.simple⟩


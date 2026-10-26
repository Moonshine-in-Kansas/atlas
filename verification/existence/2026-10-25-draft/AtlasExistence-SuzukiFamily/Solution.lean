import Atlas.LinearGroups.TypeSuzuki

open scoped BigOperators
universe u v

theorem AtlasExistence.SuzukiFamily {F : Type u} [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hm : 1 ≤ m) (hq : Nat.card F = 2^(2*m+1)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F^2*(Nat.card F^2+1)*(Nat.card F-1) ∧
      IsSimpleGroup G := by
  have h := Atlas.typeSuzuki_construction m hq hm
  exact ⟨Atlas.SuzukiFamily.Group F m, inferInstance, h.finite, h.order, h.simple⟩


import Atlas.LinearGroups.TypeG2

open scoped BigOperators
universe u v

theorem AtlasExistence.G2 {F : Type u} [Field F] [Finite F] (hq : 2 < Nat.card F) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) ∧ IsSimpleGroup G := by
  exact ⟨Atlas.G2.Model F, inferInstance, inferInstance, Atlas.G2.card_Model,
    Atlas.G2.isSimple hq⟩


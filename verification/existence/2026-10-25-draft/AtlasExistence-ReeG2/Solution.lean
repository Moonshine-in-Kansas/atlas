import Atlas.LinearGroups.TypeReeG2

open scoped BigOperators
universe u v

theorem AtlasExistence.ReeG2 {F : Type u} [Field F] [Finite F] [CharP F 3] (m : ℕ) (hm : 1 ≤ m)
    (hq : Nat.card F = 3 ^ (2 * m + 1)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 3 * (Nat.card F ^ 3 + 1) * (Nat.card F - 1) ∧ IsSimpleGroup G := by
  exact ⟨Atlas.ReeG2.Model F m, inferInstance, inferInstance, Atlas.ReeG2.order m hq,
    Atlas.ReeG2.simple m ⟨hm, hq⟩⟩


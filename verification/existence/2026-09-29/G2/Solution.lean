import Atlas.LinearGroups.TypeG2

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.G2 {F : Type u} [Field F] [Finite F] (hq : 2 < Nat.card F) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  exact ⟨Atlas.G2.Model F, inferInstance, inferInstance, Atlas.G2.card_Model,
    Atlas.G2.isSimple hq, not_comm_of_pair Atlas.G2.exists_mul_ne_mul⟩


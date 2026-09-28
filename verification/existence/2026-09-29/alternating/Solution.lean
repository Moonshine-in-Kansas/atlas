import Atlas.Families.Alternating.Basic

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.alternating (n : ℕ) (hn : 5 ≤ n) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = n.factorial / 2 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  exact ⟨Atlas.Families.Alternating.Model n, inferInstance, inferInstance,
    Atlas.Families.Alternating.card_factorial n (by omega),
    Atlas.Families.Alternating.isSimpleGroup n hn,
    not_comm_of_pair (Atlas.Families.Alternating.exists_mul_ne_mul n (by omega))⟩


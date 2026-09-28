import Atlas.Sporadic.SuzukiConstruction

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.Suz  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 448345497600 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Suzuki.Model , inferInstance, Atlas.Sporadic.Suzuki.finite ,
      Atlas.Sporadic.Suzuki.card , Atlas.Sporadic.Suzuki.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Suzuki.exists_mul_ne_mul )⟩


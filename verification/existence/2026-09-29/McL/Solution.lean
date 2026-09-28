import Atlas.Sporadic.McLaughlinConstruction

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.McL  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 898128000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.McLaughlin.Model , inferInstance, Atlas.Sporadic.McLaughlin.finite ,
      Atlas.Sporadic.McLaughlin.card , Atlas.Sporadic.McLaughlin.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.McLaughlin.exists_mul_ne_mul )⟩


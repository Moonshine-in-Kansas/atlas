import Atlas.Sporadic.Mathieu24Construction

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.M24  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 244823040 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu24.Model , inferInstance, Atlas.Sporadic.Mathieu24.finite ,
      Atlas.Sporadic.Mathieu24.card , Atlas.Sporadic.Mathieu24.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Mathieu24.exists_mul_ne_mul )⟩


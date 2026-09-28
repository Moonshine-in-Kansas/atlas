import Atlas.Sporadic.Mathieu12

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.M12  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 95040 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu12.Model Atlas.Sporadic.Mathieu12.standardDodecad, inferInstance, Atlas.Sporadic.Mathieu12.finite Atlas.Sporadic.Mathieu12.standardDodecad,
      Atlas.Sporadic.Mathieu12.card Atlas.Sporadic.Mathieu12.standardDodecad, Atlas.Sporadic.Mathieu12.isSimpleGroup Atlas.Sporadic.Mathieu12.standardDodecad,
      not_comm_of_pair (Atlas.Sporadic.Mathieu12.exists_mul_ne_mul Atlas.Sporadic.Mathieu12.standardDodecad)⟩


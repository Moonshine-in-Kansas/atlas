import Atlas.Sporadic.Mathieu11

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.M11  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 7920 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu11.Model Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint, inferInstance, Atlas.Sporadic.Mathieu11.finite Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint,
      Atlas.Sporadic.Mathieu11.card Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint, Atlas.Sporadic.Mathieu11.isSimpleGroup Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint,
      not_comm_of_pair (Atlas.Sporadic.Mathieu11.exists_mul_ne_mul Atlas.Sporadic.Mathieu12.standardDodecad Atlas.Sporadic.Mathieu12.standardPoint)⟩


import Atlas.Sporadic.Mathieu23

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.M23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 10200960 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Mathieu23.Model ((0,0),0), inferInstance, Atlas.Sporadic.Mathieu23.finite ((0,0),0),
      Atlas.Sporadic.Mathieu23.card ((0,0),0), Atlas.Sporadic.Mathieu23.isSimpleGroup ((0,0),0),
      not_comm_of_pair (Atlas.Sporadic.Mathieu23.exists_mul_ne_mul ((0,0),0))⟩


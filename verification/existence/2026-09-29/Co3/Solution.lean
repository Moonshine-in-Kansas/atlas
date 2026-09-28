import Atlas.Sporadic.Conway3Construction

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.Co3  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 495766656000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Conway3.Model , inferInstance, Atlas.Sporadic.Conway3.finite ,
      Atlas.Sporadic.Conway3.card , Atlas.Sporadic.Conway3.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Conway3.exists_mul_ne_mul )⟩


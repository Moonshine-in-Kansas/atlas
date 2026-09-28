import Atlas.Sporadic.Conway2Construction

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.Co2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 42305421312000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Conway2.Model , inferInstance, Atlas.Sporadic.Conway2.finite ,
      Atlas.Sporadic.Conway2.card , Atlas.Sporadic.Conway2.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Conway2.exists_mul_ne_mul )⟩


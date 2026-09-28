import Atlas.Sporadic.Conway1

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.Co1  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4157776806543360000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Conway1.Model , inferInstance, Atlas.Sporadic.Conway1.finite ,
      Atlas.Sporadic.Conway1.card , Atlas.Sporadic.Conway1.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Conway1.exists_mul_ne_mul )⟩


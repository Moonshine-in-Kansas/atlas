import Atlas.Sporadic.Janko2Construction

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.J2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 604800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Janko2.Model , inferInstance, Atlas.Sporadic.Janko2.finite ,
      Atlas.Sporadic.Janko2.card , Atlas.Sporadic.Janko2.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.Janko2.exists_mul_ne_mul )⟩


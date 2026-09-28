import Atlas.Sporadic.Fischer23

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.Fi23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4089470473293004800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Fischer23.Model , inferInstance, Atlas.Sporadic.Fischer23.finite ,
      Atlas.Sporadic.Fischer23.card , Atlas.Sporadic.Fischer23.simple ,
      Atlas.Sporadic.Fischer23.noncommutative⟩


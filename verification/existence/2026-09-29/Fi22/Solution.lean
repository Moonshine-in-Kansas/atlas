import Atlas.Sporadic.Fischer22

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.Fi22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 64561751654400 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Fischer22.Model , inferInstance, Atlas.Sporadic.Fischer22.finite ,
      Atlas.Sporadic.Fischer22.card , Atlas.Sporadic.Fischer22.simple ,
      Atlas.Sporadic.Fischer22.noncommutative⟩


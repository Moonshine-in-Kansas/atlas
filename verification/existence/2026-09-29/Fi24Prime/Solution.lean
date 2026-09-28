import Atlas.Sporadic.Fischer24Prime

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.Fi24Prime  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 1255205709190661721292800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.Fischer24Prime.Model , inferInstance, Atlas.Sporadic.Fischer24Prime.finite ,
      Atlas.Sporadic.Fischer24Prime.card , Atlas.Sporadic.Fischer24Prime.simple ,
      Atlas.Sporadic.Fischer24Prime.noncommutative⟩


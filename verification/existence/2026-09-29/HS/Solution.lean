import Atlas.Sporadic.HigmanSimsConstruction

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.HS  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 44352000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
    exact ⟨Atlas.Sporadic.HigmanSims.Model , inferInstance, Atlas.Sporadic.HigmanSims.finite ,
      Atlas.Sporadic.HigmanSims.card , Atlas.Sporadic.HigmanSims.isSimpleGroup ,
      not_comm_of_pair (Atlas.Sporadic.HigmanSims.exists_mul_ne_mul )⟩


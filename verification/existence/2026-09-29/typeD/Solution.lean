import Atlas.LinearGroups.Orthogonal.DConstruction

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.typeD {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 4 ≤ n) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1)) * (Nat.card F ^ n - 1) *
      ∏ i ∈ Finset.range (n - 1), (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 4 (Nat.card F ^ n - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  exact ⟨Atlas.Orthogonal.DPlus n F, inferInstance, inferInstance,
    Atlas.Orthogonal.DPlus_card n hn, Atlas.Orthogonal.DPlus_simple n hn,
    Atlas.Orthogonal.DPlus_noncommutative n hn⟩


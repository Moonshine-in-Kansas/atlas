import Atlas.LinearGroups.TypeA

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.typeA {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (h2 : (n, Nat.card F) ≠ (2, 2)) (h3 : (n, Nat.card F) ≠ (2, 3)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Nat.card F ^ i - 1)) / Nat.gcd n (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  obtain ⟨G, g, _, hf, hs, ha, ho, _⟩ := Atlas.exists_typeA (F := F) n hn h2 h3
  exact ⟨G, g, hf, ho, hs, ha⟩


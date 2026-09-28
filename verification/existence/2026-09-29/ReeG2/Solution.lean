import Atlas.LinearGroups.TypeReeG2

open scoped BigOperators
universe u

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasExistence.ReeG2 {F : Type u} [Field F] [Finite F] [CharP F 3] (m : ℕ) (hm : 1 ≤ m)
    (hq : Nat.card F = 3 ^ (2 * m + 1)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 3 * (Nat.card F ^ 3 + 1) * (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  exact ⟨Atlas.ReeG2.Model F m, inferInstance, inferInstance, Atlas.ReeG2.order m hq,
    Atlas.ReeG2.simple m ⟨hm, hq⟩, not_comm_of_pair (Atlas.ReeG2.model_noncommutative m hq)⟩


import Atlas.LinearGroups.TypeC

open scoped BigOperators
universe u v

theorem AtlasExistence.typeC {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : (n = 1 ∧ 3 < Nat.card F) ∨ (2 ≤ n ∧ (n, Nat.card F) ≠ (2, 2))) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G := by
  refine ⟨Atlas.Symplectic.PSp n F, inferInstance, inferInstance, ?_,
    Atlas.Symplectic.simple_of_good h⟩
  apply Atlas.Symplectic.card_psp
  rcases h with h | h <;> omega


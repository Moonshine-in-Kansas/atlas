import Atlas.LinearGroups.Type2D

open scoped BigOperators
universe u v

theorem AtlasExistence.type2D {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 4 ≤ n) :
  ∃ (G : Type (max u v)) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F^(n*(n-1)) * (Nat.card F^n+1) *
      ∏ i ∈ Finset.range (n-1), (Nat.card F^(2*(i+1))-1)) /
      Nat.gcd 4 (Nat.card F^n+1) ∧ IsSimpleGroup G := by
  exact ⟨Atlas.Orthogonal.DMinus n F K hdeg, inferInstance, inferInstance,
    Atlas.Orthogonal.Minus.family_order hdeg n (by omega),
    Atlas.Orthogonal.Minus.family_simple hdeg n hn⟩


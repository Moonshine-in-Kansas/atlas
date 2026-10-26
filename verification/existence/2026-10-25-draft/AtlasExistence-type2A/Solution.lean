import Atlas.LinearGroups.Type2A

open scoped BigOperators
universe u v

theorem AtlasExistence.type2A {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 2 ≤ n)
    (h22 : (n, Nat.card F) ≠ (2,2)) (h23 : (n, Nat.card F) ≠ (2,3))
    (h32 : (n, Nat.card F) ≠ (3,2)) :
  ∃ (G : Type v) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n*(n-1)/2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then Nat.card F^i-1 else Nat.card F^i+1)) /
      Nat.gcd n (Nat.card F+1) ∧ IsSimpleGroup G := by
  have h := Atlas.type2A_construction hdeg n hn ⟨hn,h22,h23,h32⟩
  exact ⟨Atlas.Unitary.PSU F K n hdeg, inferInstance, h.finite,
    h.order, h.simple⟩


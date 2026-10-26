import Atlas.LinearGroups.Chevalley.ModelAOrder
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

open scoped BigOperators
universe u

theorem AtlasExistenceChevalley.A {F : Type u} [Field F] [Finite F] (r : ℕ) (hr : 1 ≤ r)
    (h2 : (r, Nat.card F) ≠ (1, 2)) (h3 : (r, Nat.card F) ≠ (1, 3)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (r * (r + 1) / 2) * ∏ i ∈ Finset.range r, (Nat.card F ^ (i + 2) - 1)) / Nat.gcd (r + 1) (Nat.card F - 1) ∧ IsSimpleGroup G := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  refine ⟨Atlas.Chevalley.Model (.A r hr) F, inferInstance, inferInstance,
    Atlas.Chevalley.model_A_card r hr F, ?_⟩
  apply Atlas.Chevalley.model_isSimpleGroup_of_good
  refine ⟨Fintype.one_lt_card, ?_⟩
  change r ≠ 1 ∨ (Fintype.card F ≠ 2 ∧ Fintype.card F ≠ 3)
  simp only [Nat.card_eq_fintype_card (α := F)] at h2 h3
  by_cases h : r = 1
  · right
    constructor
    · intro hq
      exact h2 (Prod.ext h hq)
    · intro hq
      exact h3 (Prod.ext h hq)
  · exact Or.inl h

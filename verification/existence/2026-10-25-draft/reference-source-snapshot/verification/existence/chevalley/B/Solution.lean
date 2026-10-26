import Atlas.LinearGroups.Chevalley.ModelBCOrder
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

open scoped BigOperators
universe u

theorem AtlasExistenceChevalley.B {F : Type u} [Field F] [Finite F] (r : ℕ) (hr : 2 ≤ r) (h2 : (r, Nat.card F) ≠ (2, 2)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (r ^ 2) * ∏ i ∈ Finset.range r, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  refine ⟨Atlas.Chevalley.Model (.B r hr) F, inferInstance, inferInstance,
    Atlas.Chevalley.model_B_card r hr F, ?_⟩
  apply Atlas.Chevalley.model_isSimpleGroup_of_good
  refine ⟨Fintype.one_lt_card, ?_⟩
  change r ≠ 2 ∨ Fintype.card F ≠ 2
  simp only [Nat.card_eq_fintype_card (α := F)] at h2
  by_cases h : r = 2
  · right
    intro hq
    exact h2 (Prod.ext h hq)
  · exact Or.inl h

import Atlas.LinearGroups.Chevalley.ModelDOrder
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

open scoped BigOperators
universe u

theorem AtlasExistenceChevalley.D {F : Type u} [Field F] [Finite F] (r : ℕ) (hr : 4 ≤ r) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (r * (r - 1)) * (Nat.card F ^ r - 1) * ∏ i ∈ Finset.range (r - 1), (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 4 (Nat.card F ^ r - 1) ∧ IsSimpleGroup G := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  refine ⟨Atlas.Chevalley.Model (.D r hr) F, inferInstance, inferInstance,
    Atlas.Chevalley.model_D_card r hr F, ?_⟩
  apply Atlas.Chevalley.model_isSimpleGroup_of_good
  refine ⟨Fintype.one_lt_card, ?_⟩
  trivial

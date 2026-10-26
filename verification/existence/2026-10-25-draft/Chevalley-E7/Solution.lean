import Atlas.LinearGroups.Chevalley.ModelE7Order
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

open scoped BigOperators
universe u

theorem AtlasExistenceChevalley.E7 {F : Type u} [Field F] [Finite F]  :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ 63 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 8 - 1) * (Nat.card F ^ 10 - 1) * (Nat.card F ^ 12 - 1) * (Nat.card F ^ 14 - 1) * (Nat.card F ^ 18 - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  refine ⟨Atlas.Chevalley.Model .E7 F, inferInstance, inferInstance,
    Atlas.Chevalley.model_E7_card F, ?_⟩
  apply Atlas.Chevalley.model_isSimpleGroup_of_good
  refine ⟨Fintype.one_lt_card, ?_⟩
  trivial

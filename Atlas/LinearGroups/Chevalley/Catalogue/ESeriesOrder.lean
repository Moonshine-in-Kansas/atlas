import Atlas.LinearGroups.Chevalley.Catalogue.ESeriesConstruction
import Atlas.LinearGroups.Chevalley.ModelE6Order
import Atlas.LinearGroups.Chevalley.ModelE7Order
import Atlas.LinearGroups.Chevalley.ModelE8Order

/-! Separate catalogue order evidence for the same three actual carriers. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem E6_order (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Nat.card (E6 K) =
      Nat.card K ^ 36 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 5 - 1) *
        (Nat.card K ^ 6 - 1) * (Nat.card K ^ 8 - 1) * (Nat.card K ^ 9 - 1) *
        (Nat.card K ^ 12 - 1) / Nat.gcd 3 (Nat.card K - 1) := by
  letI : Finite K := hK
  exact model_E6_card K

theorem E7_order (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Nat.card (E7 K) =
      Nat.card K ^ 63 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 6 - 1) *
        (Nat.card K ^ 8 - 1) * (Nat.card K ^ 10 - 1) * (Nat.card K ^ 12 - 1) *
        (Nat.card K ^ 14 - 1) * (Nat.card K ^ 18 - 1) / Nat.gcd 2 (Nat.card K - 1) := by
  letI : Finite K := hK
  exact model_E7_card K

theorem E8_order (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Nat.card (E8 K) =
      Nat.card K ^ 120 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 8 - 1) *
        (Nat.card K ^ 12 - 1) * (Nat.card K ^ 14 - 1) * (Nat.card K ^ 18 - 1) *
        (Nat.card K ^ 20 - 1) * (Nat.card K ^ 24 - 1) * (Nat.card K ^ 30 - 1) := by
  letI : Finite K := hK
  exact model_E8_card K

end Atlas.Chevalley.Catalogue

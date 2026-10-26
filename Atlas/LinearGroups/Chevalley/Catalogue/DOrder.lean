import Atlas.LinearGroups.Chevalley.Catalogue.DConstruction
import Atlas.LinearGroups.Chevalley.ModelDOrder

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem D_order (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (hK : DFieldDomain r hr K) :
    Nat.card (D r hr K) =
      (Nat.card K ^ (r * (r - 1)) * (Nat.card K ^ r - 1) *
        ∏ d ∈ Finset.range (r - 1), (Nat.card K ^ (2 * (d + 1)) - 1)) /
          Nat.gcd 4 (Nat.card K ^ r - 1) := by
  letI : Finite K := hK
  exact model_D_card r hr K

end Atlas.Chevalley.Catalogue

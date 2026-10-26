import Atlas.LinearGroups.Chevalley.Catalogue.ACConstruction
import Atlas.LinearGroups.Chevalley.ModelAOrder
import Atlas.LinearGroups.Chevalley.ModelBCOrder

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem A_order (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (hK : AFieldDomain r hr K) :
    Nat.card (A r hr K) =
      (Nat.card K ^ (r * (r + 1) / 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (d + 2) - 1)) /
          Nat.gcd (r + 1) (Nat.card K - 1) := by
  letI : Finite K := hK
  exact model_A_card r hr K

theorem C_order (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : CFieldDomain n hn K) :
    Nat.card (C n hn K) =
      (Nat.card K ^ ((n + 1) ^ 2) *
        ∏ d ∈ Finset.range (n + 1), (Nat.card K ^ (2 * (d + 1)) - 1)) /
          Nat.gcd 2 (Nat.card K - 1) := by
  letI : Finite K := hK
  exact model_C_card (n + 1) hn K

end Atlas.Chevalley.Catalogue

import Atlas.LinearGroups.Chevalley.Catalogue.BConstruction
import Atlas.LinearGroups.Chevalley.ModelBCOrder

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem B_order (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : BFieldDomain n hn K) :
    Nat.card (B n hn K) =
      (Nat.card K ^ ((n + 1) ^ 2) *
        ∏ d ∈ Finset.range (n + 1), (Nat.card K ^ (2 * (d + 1)) - 1)) /
          Nat.gcd 2 (Nat.card K - 1) := by
  letI : Finite K := hK
  exact model_B_card (n + 1) hn K

end Atlas.Chevalley.Catalogue

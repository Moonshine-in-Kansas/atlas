import Atlas.LinearGroups.Chevalley.Catalogue.DConstruction
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- For D, Good is 2 ≤ |K| ∧ True, automatic over every finite field. -/
def DGoodDomain (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K] : Prop :=
  DFieldDomain r hr K ∧ (RootType.D r hr).Good (Nat.card K)

theorem D_simple (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (hK : DGoodDomain r hr K) : IsSimpleGroup (D r hr K) := by
  letI : Finite K := hK.1
  letI : Fintype K := Fintype.ofFinite K
  apply model_isSimpleGroup_of_good (.D r hr) K
  simpa only [Nat.card_eq_fintype_card (α := K)] using hK.2

end Atlas.Chevalley.Catalogue

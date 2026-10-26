import Atlas.LinearGroups.Chevalley.Catalogue.BConstruction
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- The carrier is unchanged at B2(F2); only simplicity excludes that parameter. -/
def BGoodDomain (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K] : Prop :=
  BFieldDomain n hn K ∧ (RootType.B (n + 1) hn).Good (Nat.card K)

theorem B_simple (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : BGoodDomain n hn K) : IsSimpleGroup (B n hn K) := by
  letI : Finite K := hK.1
  letI : Fintype K := Fintype.ofFinite K
  apply model_isSimpleGroup_of_good (.B (n + 1) hn) K
  simpa only [Nat.card_eq_fintype_card (α := K)] using hK.2

end Atlas.Chevalley.Catalogue

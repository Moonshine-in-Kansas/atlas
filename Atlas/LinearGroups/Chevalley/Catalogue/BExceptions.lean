import Atlas.LinearGroups.Chevalley.Catalogue.BConstruction
import Atlas.LinearGroups.Chevalley.ModelBCSimplicityIffGood

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem B_exceptions (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : BFieldDomain n hn K) :
    IsSimpleGroup (B n hn K) ↔ (RootType.B (n + 1) hn).Good (Nat.card K) := by
  letI : Finite K := hK
  exact model_B_isSimpleGroup_iff_good (n + 1) hn K

end Atlas.Chevalley.Catalogue

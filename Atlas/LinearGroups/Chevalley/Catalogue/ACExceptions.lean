import Atlas.LinearGroups.Chevalley.Catalogue.ACConstruction
import Atlas.LinearGroups.Chevalley.ModelASimplicityIffGood
import Atlas.LinearGroups.Chevalley.ModelBCSimplicityIffGood

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem A_exceptions (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (hK : AFieldDomain r hr K) :
    IsSimpleGroup (A r hr K) ↔ (RootType.A r hr).Good (Nat.card K) := by
  letI : Finite K := hK
  exact model_A_isSimpleGroup_iff_good r hr K

theorem C_exceptions (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : CFieldDomain n hn K) :
    IsSimpleGroup (C n hn K) ↔ (RootType.C (n + 1) hn).Good (Nat.card K) := by
  letI : Finite K := hK
  exact model_C_isSimpleGroup_iff_good (n + 1) hn K

end Atlas.Chevalley.Catalogue

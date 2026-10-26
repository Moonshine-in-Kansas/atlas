import Atlas.LinearGroups.Chevalley.Catalogue.ACConstruction
import Atlas.LinearGroups.Chevalley.ModelFiniteCenter

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem A_center (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (hK : AFieldDomain r hr K) : Subgroup.center (A r hr K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField (.A r hr) K

theorem C_center (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : CFieldDomain n hn K) : Subgroup.center (C n hn K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField (.C (n + 1) hn) K

end Atlas.Chevalley.Catalogue

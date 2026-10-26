import Atlas.LinearGroups.Chevalley.Catalogue.DConstruction
import Atlas.LinearGroups.Chevalley.ModelFiniteCenter

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem D_center (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (hK : DFieldDomain r hr K) : Subgroup.center (D r hr K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField (.D r hr) K

end Atlas.Chevalley.Catalogue

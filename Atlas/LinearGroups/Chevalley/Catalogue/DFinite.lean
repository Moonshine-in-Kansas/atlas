import Atlas.LinearGroups.Chevalley.Catalogue.DConstruction

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem D_finite (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (hK : DFieldDomain r hr K) : Finite (D r hr K) := by
  letI : Finite K := hK
  exact modelFinite (.D r hr) K

end Atlas.Chevalley.Catalogue

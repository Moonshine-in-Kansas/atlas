import Atlas.LinearGroups.Chevalley.Catalogue.DConstruction

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem D_nonabelian (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (_hK : DFieldDomain r hr K) : ¬ IsMulCommutative (D r hr K) :=
  model_not_commutative (.D r hr) K

end Atlas.Chevalley.Catalogue

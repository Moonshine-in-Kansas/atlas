import Atlas.LinearGroups.Chevalley.Catalogue.BConstruction

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem B_finite (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : BFieldDomain n hn K) : Finite (B n hn K) := by
  letI : Finite K := hK
  exact modelFinite (.B (n + 1) hn) K

end Atlas.Chevalley.Catalogue

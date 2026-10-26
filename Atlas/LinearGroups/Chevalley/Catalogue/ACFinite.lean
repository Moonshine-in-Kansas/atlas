import Atlas.LinearGroups.Chevalley.Catalogue.ACConstruction

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem A_finite (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (hK : AFieldDomain r hr K) : Finite (A r hr K) := by
  letI : Finite K := hK
  exact modelFinite (.A r hr) K

theorem C_finite (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : CFieldDomain n hn K) : Finite (C n hn K) := by
  letI : Finite K := hK
  exact modelFinite (.C (n + 1) hn) K

end Atlas.Chevalley.Catalogue

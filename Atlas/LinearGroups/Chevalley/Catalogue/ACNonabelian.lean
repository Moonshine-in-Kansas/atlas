import Atlas.LinearGroups.Chevalley.Catalogue.ACConstruction

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem A_nonabelian (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (_hK : AFieldDomain r hr K) : ¬ IsMulCommutative (A r hr K) :=
  model_not_commutative (.A r hr) K

theorem C_nonabelian (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (_hK : CFieldDomain n hn K) : ¬ IsMulCommutative (C n hn K) :=
  model_not_commutative (.C (n + 1) hn) K

end Atlas.Chevalley.Catalogue

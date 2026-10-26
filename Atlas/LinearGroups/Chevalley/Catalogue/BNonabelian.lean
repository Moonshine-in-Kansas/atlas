import Atlas.LinearGroups.Chevalley.Catalogue.BConstruction

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem B_nonabelian (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (_hK : BFieldDomain n hn K) : ¬ IsMulCommutative (B n hn K) :=
  model_not_commutative (.B (n + 1) hn) K

end Atlas.Chevalley.Catalogue

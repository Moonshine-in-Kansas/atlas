import Atlas.LinearGroups.Chevalley.Catalogue.BConstruction
import Atlas.LinearGroups.Chevalley.ModelFiniteCenter

/-! Source-only catalogue interface candidate; not compiled or registered. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem B_center (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : BFieldDomain n hn K) : Subgroup.center (B n hn K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField (.B (n + 1) hn) K

end Atlas.Chevalley.Catalogue

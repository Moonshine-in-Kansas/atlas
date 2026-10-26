import Atlas.LinearGroups.Chevalley.Catalogue.ESeriesConstruction
import Atlas.LinearGroups.Chevalley.ModelFiniteCenter

/-! Separate catalogue center evidence for the same three actual carriers. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- The center of the adjoint elementary carrier is trivial, not the cover gcd. -/
theorem E6_center (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Subgroup.center (E6 K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField .E6 K

/-- The center of the adjoint elementary carrier is trivial, not the cover gcd. -/
theorem E7_center (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Subgroup.center (E7 K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField .E7 K

/-- The center of the adjoint elementary carrier is trivial, not the cover gcd. -/
theorem E8_center (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Subgroup.center (E8 K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField .E8 K

end Atlas.Chevalley.Catalogue

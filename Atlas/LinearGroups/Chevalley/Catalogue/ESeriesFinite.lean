import Atlas.LinearGroups.Chevalley.Catalogue.ESeriesConstruction

/-! Separate catalogue finite evidence for the same three actual carriers. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem E6_finite (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Finite (E6 K) := by
  letI : Finite K := hK
  exact modelFinite .E6 K

theorem E7_finite (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Finite (E7 K) := by
  letI : Finite K := hK
  exact modelFinite .E7 K

theorem E8_finite (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    Finite (E8 K) := by
  letI : Finite K := hK
  exact modelFinite .E8 K

end Atlas.Chevalley.Catalogue

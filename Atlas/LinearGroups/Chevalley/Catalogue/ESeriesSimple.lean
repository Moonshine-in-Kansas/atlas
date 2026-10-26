import Atlas.LinearGroups.Chevalley.Catalogue.ESeriesConstruction
import Atlas.LinearGroups.Chevalley.ModelSimplicityGood

/-! Separate catalogue simple evidence for the same three actual carriers. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem E6_simple (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    IsSimpleGroup (E6 K) := by
  letI : Finite K := hK
  letI : Fintype K := Fintype.ofFinite K
  exact model_isSimpleGroup_of_good .E6 K ⟨Fintype.one_lt_card, trivial⟩

theorem E7_simple (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    IsSimpleGroup (E7 K) := by
  letI : Finite K := hK
  letI : Fintype K := Fintype.ofFinite K
  exact model_isSimpleGroup_of_good .E7 K ⟨Fintype.one_lt_card, trivial⟩

theorem E8_simple (K : Type*) [Field K] (hK : FiniteFieldDomain K) :
    IsSimpleGroup (E8 K) := by
  letI : Finite K := hK
  letI : Fintype K := Fintype.ofFinite K
  exact model_isSimpleGroup_of_good .E8 K ⟨Fintype.one_lt_card, trivial⟩

end Atlas.Chevalley.Catalogue

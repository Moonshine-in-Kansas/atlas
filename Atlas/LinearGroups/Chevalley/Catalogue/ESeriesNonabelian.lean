import Atlas.LinearGroups.Chevalley.Catalogue.ESeriesConstruction

/-! Separate catalogue nonabelian evidence for the same three actual carriers. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem E6_nonabelian (K : Type*) [Field K] (_hK : FiniteFieldDomain K) :
    ¬ IsMulCommutative (E6 K) :=
  model_not_commutative .E6 K

theorem E7_nonabelian (K : Type*) [Field K] (_hK : FiniteFieldDomain K) :
    ¬ IsMulCommutative (E7 K) :=
  model_not_commutative .E7 K

theorem E8_nonabelian (K : Type*) [Field K] (_hK : FiniteFieldDomain K) :
    ¬ IsMulCommutative (E8 K) :=
  model_not_commutative .E8 K

end Atlas.Chevalley.Catalogue

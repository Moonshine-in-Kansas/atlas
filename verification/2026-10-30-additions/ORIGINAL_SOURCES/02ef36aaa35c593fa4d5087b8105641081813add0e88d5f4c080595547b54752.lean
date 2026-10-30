import ComparisonWork.G2Construction

/-! Source-only G₂ registration draft; this property also includes q = 2. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem G2_nonabelian (K : Type*) [Field K] (_hK : G2FieldDomain K) :
    ¬ IsMulCommutative (G2 K) :=
  model_not_commutative .G2 K

end Atlas.Chevalley.Catalogue

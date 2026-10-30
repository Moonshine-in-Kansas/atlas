import ComparisonWork.G2Construction

/-! Source-only G₂ registration draft; no compilation or audit is claimed. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem G2_finite (K : Type*) [Field K] (hK : G2FieldDomain K) :
    Finite (G2 K) := by
  letI : Finite K := hK
  exact modelFinite .G2 K

end Atlas.Chevalley.Catalogue

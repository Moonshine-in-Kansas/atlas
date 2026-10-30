import ComparisonWork.G2Construction
import Atlas.LinearGroups.Chevalley.ModelFiniteCenter

/-! Source-only G₂ registration draft; this is the center of the adjoint carrier. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem G2_center (K : Type*) [Field K] (hK : G2FieldDomain K) :
    Subgroup.center (G2 K) = ⊥ := by
  letI : Finite K := hK
  exact model_center_eq_bot_finiteField .G2 K

end Atlas.Chevalley.Catalogue

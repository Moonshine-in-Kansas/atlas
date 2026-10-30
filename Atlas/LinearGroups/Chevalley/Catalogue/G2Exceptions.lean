import Atlas.LinearGroups.Chevalley.Catalogue.G2Construction
import Atlas.LinearGroups.Chevalley.ModelSimplicityIffGood

/-! Source-only G₂ registration draft; the binary exception retains the full group. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem G2_exceptions (K : Type*) [Field K] (hK : G2FieldDomain K) :
    IsSimpleGroup (G2 K) ↔ RootType.G2.Good (Nat.card K) := by
  letI : Finite K := hK
  exact model_isSimpleGroup_iff_good .G2 K

end Atlas.Chevalley.Catalogue

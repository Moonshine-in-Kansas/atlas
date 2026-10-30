import ComparisonWork.G2Construction
import Atlas.LinearGroups.Chevalley.ModelG2Order

/-! Source-only G₂ registration draft; independent of the octonion comparison. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

theorem G2_order (K : Type*) [Field K] (hK : G2FieldDomain K) :
    Nat.card (G2 K) = Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) *
      (Nat.card K ^ 2 - 1) := by
  letI : Finite K := hK
  exact model_G2_card K

end Atlas.Chevalley.Catalogue

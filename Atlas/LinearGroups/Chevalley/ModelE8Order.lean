import Atlas.LinearGroups.Chevalley.RootData.E8PoincareNumerator
import Atlas.LinearGroups.Chevalley.ModelBruhatOrder

/-! The actual uniform-engine E8 companion and adjoint orders over every
finite field. The root-Weyl factor is derived from the 240-root orbit and E7
parabolic. The adjoint formula uses the separately proved center factor 1;
no old E8 model, simplicity range or order recognition is used. -/
noncomputable section
namespace Atlas.Chevalley
open RootData

theorem selectedWeightCompanion_E8_card (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion .E8 K) =
      Nat.card K ^ 120 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 8 - 1) *
        (Nat.card K ^ 12 - 1) * (Nat.card K ^ 14 - 1) * (Nat.card K ^ 18 - 1) *
        (Nat.card K ^ 20 - 1) * (Nat.card K ^ 24 - 1) * (Nat.card K ^ 30 - 1) := by
  have h := selectedWeightCompanion_card_eq_weylSum .E8 K
  change Nat.card (SelectedWeightCompanion .E8 K) =
    Nat.card K ^ 120 * (Nat.card K - 1) ^ 8 *
      rootWeylPoincareEval E8Data.pairing E8Data.base (Nat.card K) at h
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [mul_assoc, E8E7.rootWeylPoincareEval_E8_numerator _ hq] at h
  simpa only [mul_assoc] using h

theorem model_E8_card (K : Type*) [Field K] [Finite K] :
    Nat.card (Model .E8 K) =
      Nat.card K ^ 120 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 8 - 1) *
        (Nat.card K ^ 12 - 1) * (Nat.card K ^ 14 - 1) * (Nat.card K ^ 18 - 1) *
        (Nat.card K ^ 20 - 1) * (Nat.card K ^ 24 - 1) * (Nat.card K ^ 30 - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have h := model_centerFactor_mul_card_eq_weylSum .E8 K
  change 1 * Nat.card (Model .E8 K) =
    Fintype.card K ^ 120 * (Fintype.card K - 1) ^ 8 *
      rootWeylPoincareEval E8Data.pairing E8Data.base (Fintype.card K) at h
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [one_mul, mul_assoc, E8E7.rootWeylPoincareEval_E8_numerator _ hq] at h
  simpa only [Nat.card_eq_fintype_card (α := K), mul_assoc] using h

end Atlas.Chevalley

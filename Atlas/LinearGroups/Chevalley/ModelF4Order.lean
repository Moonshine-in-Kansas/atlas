import Atlas.LinearGroups.Chevalley.RootData.F4PoincareNumerator
import Atlas.LinearGroups.Chevalley.ModelBruhatOrder

/-! The actual uniform-engine F4 companion and adjoint orders over every
finite field. The root-Weyl factor is derived from the24-root orbit and B3
parabolic. The adjoint formula uses the separately proved center factor1;
no old Albert F4 model, simplicity range or order recognition is used. -/
noncomputable section
namespace Atlas.Chevalley
open RootData

theorem selectedWeightCompanion_F4_card (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion .F4 K) =
      Nat.card K ^ 24 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 6 - 1) *
        (Nat.card K ^ 8 - 1) * (Nat.card K ^ 12 - 1) := by
  have h := selectedWeightCompanion_card_eq_weylSum .F4 K
  change Nat.card (SelectedWeightCompanion .F4 K) =
    Nat.card K ^ 24 * (Nat.card K - 1) ^ 4 *
      rootWeylPoincareEval F4Data.pairing F4Data.base (Nat.card K) at h
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [mul_assoc, F4B3.rootWeylPoincareEval_F4_numerator _ hq] at h
  simpa only [mul_assoc] using h

theorem model_F4_card (K : Type*) [Field K] [Finite K] :
    Nat.card (Model .F4 K) =
      Nat.card K ^ 24 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 6 - 1) *
        (Nat.card K ^ 8 - 1) * (Nat.card K ^ 12 - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have h := model_centerFactor_mul_card_eq_weylSum .F4 K
  change 1 * Nat.card (Model .F4 K) =
    Fintype.card K ^ 24 * (Fintype.card K - 1) ^ 4 *
      rootWeylPoincareEval F4Data.pairing F4Data.base (Fintype.card K) at h
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [one_mul, mul_assoc, F4B3.rootWeylPoincareEval_F4_numerator _ hq] at h
  simpa only [Nat.card_eq_fintype_card (α := K), mul_assoc] using h

end Atlas.Chevalley

import Atlas.LinearGroups.Chevalley.RootData.G2PoincareProduct
import Atlas.LinearGroups.Chevalley.ModelBruhatOrder

/-! Explicit order of the actual uniform-engine G2 adjoint model and selected
companion over every finite field, including the binary and ternary fields.
No previously constructed octonion G2 model or order theorem is used. -/
noncomputable section
namespace Atlas.Chevalley
open RootData

theorem selectedWeightCompanion_G2_card (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion .G2 K) =
      Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := by
  have h := selectedWeightCompanion_card_eq_weylSum .G2 K
  change Nat.card (SelectedWeightCompanion .G2 K) =
    Nat.card K ^ 6 * (Nat.card K - 1) ^ 2 *
      rootWeylPoincareEval G2Data.pairing G2Data.base (Nat.card K) at h
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [mul_assoc, G2Parabolic.rootWeylPoincareEval_g2_product _ hq, ← mul_assoc] at h
  exact h

theorem model_G2_card (K : Type*) [Field K] [Finite K] :
    Nat.card (Model .G2 K) =
      Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have h := model_centerFactor_mul_card_eq_weylSum .G2 K
  change 1 * Nat.card (Model .G2 K) =
    Fintype.card K ^ 6 * (Fintype.card K - 1) ^ 2 *
      rootWeylPoincareEval G2Data.pairing G2Data.base (Fintype.card K) at h
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [one_mul, mul_assoc, G2Parabolic.rootWeylPoincareEval_g2_product _ hq,
    ← mul_assoc] at h
  simpa only [Nat.card_eq_fintype_card (α := K)] using h

end Atlas.Chevalley

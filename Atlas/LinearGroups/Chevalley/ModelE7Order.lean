import Atlas.LinearGroups.Chevalley.RootData.E7PoincareNumerator
import Atlas.LinearGroups.Chevalley.ModelBruhatOrder

/-! Orders of the actual uniform E7 companion and its actual full-center
quotient over every finite field. The quotient divisor is gcd(2,q-1). -/
noncomputable section
namespace Atlas.Chevalley
open RootData

theorem selectedWeightCompanion_E7_card (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion .E7 K) =
      Nat.card K ^ 63 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 6 - 1) *
      (Nat.card K ^ 8 - 1) * (Nat.card K ^ 10 - 1) *
      (Nat.card K ^ 12 - 1) * (Nat.card K ^ 14 - 1) * (Nat.card K ^ 18 - 1) := by
  have h := selectedWeightCompanion_card_eq_weylSum .E7 K
  change Nat.card (SelectedWeightCompanion .E7 K) =
    Nat.card K ^ 63 * (Nat.card K - 1) ^ 7 *
      rootWeylPoincareEval E7Data.pairing E7Data.base (Nat.card K) at h
  rw [mul_assoc, E7E6.rootWeylPoincareEval_E7_numerator _ Nat.card_pos] at h
  simpa only [mul_assoc] using h

theorem model_E7_centerFactor_mul_card (K : Type*) [Field K] [Finite K] :
    Nat.gcd 2 (Nat.card K - 1) * Nat.card (Model .E7 K) =
      Nat.card K ^ 63 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 6 - 1) *
      (Nat.card K ^ 8 - 1) * (Nat.card K ^ 10 - 1) *
      (Nat.card K ^ 12 - 1) * (Nat.card K ^ 14 - 1) * (Nat.card K ^ 18 - 1) := by
  let : Fintype K := Fintype.ofFinite K
  have h := model_centerFactor_mul_card_eq_weylSum .E7 K
  change Nat.gcd 2 (Fintype.card K - 1) * Nat.card (Model .E7 K) =
    Fintype.card K ^ 63 * (Fintype.card K - 1) ^ 7 *
      rootWeylPoincareEval E7Data.pairing E7Data.base (Fintype.card K) at h
  rw [mul_assoc, E7E6.rootWeylPoincareEval_E7_numerator _ Fintype.card_pos] at h
  simpa only [Nat.card_eq_fintype_card (α := K), mul_assoc] using h

theorem model_E7_card (K : Type*) [Field K] [Finite K] :
    Nat.card (Model .E7 K) =
      (Nat.card K ^ 63 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 6 - 1) *
      (Nat.card K ^ 8 - 1) * (Nat.card K ^ 10 - 1) *
      (Nat.card K ^ 12 - 1) * (Nat.card K ^ 14 - 1) *
      (Nat.card K ^ 18 - 1)) / Nat.gcd 2 (Nat.card K - 1) := by
  rw [← model_E7_centerFactor_mul_card K]
  exact (Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 2))).symm

end Atlas.Chevalley

import Atlas.LinearGroups.Chevalley.RootData.E6PoincareNumerator
import Atlas.LinearGroups.Chevalley.ModelBruhatOrder

/-! Orders of the actual uniform E6 companion and its actual full-center
quotient over every finite field. The quotient divisor is gcd(3,q-1). -/
noncomputable section
namespace Atlas.Chevalley
open Classical RootData
local instance : Fintype E6Data.Root := Fintype.ofFinite _

theorem selectedWeightCompanion_E6_card (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion .E6 K) =
      Nat.card K ^ 36 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 5 - 1) *
      (Nat.card K ^ 6 - 1) * (Nat.card K ^ 8 - 1) *
      (Nat.card K ^ 9 - 1) * (Nat.card K ^ 12 - 1) := by
  have h := selectedWeightCompanion_card_eq_weylSum .E6 K
  change Nat.card (SelectedWeightCompanion .E6 K) =
    Nat.card K ^ 36 * (Nat.card K - 1) ^ 6 *
      rootWeylPoincareEval E6Data.pairing E6Data.base (Nat.card K) at h
  rw [mul_assoc, E6D5.rootWeylPoincareEval_E6_numerator _ Nat.card_pos] at h
  simpa only [mul_assoc] using h

theorem model_E6_centerFactor_mul_card (K : Type*) [Field K] [Finite K] :
    Nat.gcd 3 (Nat.card K - 1) * Nat.card (Model .E6 K) =
      Nat.card K ^ 36 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 5 - 1) *
      (Nat.card K ^ 6 - 1) * (Nat.card K ^ 8 - 1) *
      (Nat.card K ^ 9 - 1) * (Nat.card K ^ 12 - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have h := model_centerFactor_mul_card_eq_weylSum .E6 K
  change Nat.gcd 3 (Fintype.card K - 1) * Nat.card (Model .E6 K) =
    Fintype.card K ^ 36 * (Fintype.card K - 1) ^ 6 *
      rootWeylPoincareEval E6Data.pairing E6Data.base (Fintype.card K) at h
  rw [mul_assoc, E6D5.rootWeylPoincareEval_E6_numerator _ Fintype.card_pos] at h
  simpa only [Nat.card_eq_fintype_card (α := K), mul_assoc] using h

theorem model_E6_card (K : Type*) [Field K] [Finite K] :
    Nat.card (Model .E6 K) =
      (Nat.card K ^ 36 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 5 - 1) *
      (Nat.card K ^ 6 - 1) * (Nat.card K ^ 8 - 1) *
      (Nat.card K ^ 9 - 1) * (Nat.card K ^ 12 - 1)) / Nat.gcd 3 (Nat.card K - 1) := by
  rw [← model_E6_centerFactor_mul_card K]
  exact (Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 3))).symm

end Atlas.Chevalley

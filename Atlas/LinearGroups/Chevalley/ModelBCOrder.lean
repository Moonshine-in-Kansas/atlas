import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionBCOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterCounts

/-! Orders of the actual type-B and type-C adjoint models, obtained from the
independently constructed selected companions and their proved full centers.
All finite characteristics are included. No old model comparison is asserted. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_B_centerFactor_mul_card (r : ℕ) (hr : 2 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.gcd 2 (Nat.card K - 1) * Nat.card (Model (.B r hr) K) =
      Nat.card K ^ (r ^ 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (2 * (d + 1)) - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have h := selectedWeightCompanion_card_eq_model_mul_center (.B r hr) K
  rw [selectedWeightCompanion_B_card, selectedWeightCompanion_B_center_card] at h
  simpa only [Nat.card_eq_fintype_card (α := K), mul_comm] using h.symm

theorem model_C_centerFactor_mul_card (r : ℕ) (hr : 2 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.gcd 2 (Nat.card K - 1) * Nat.card (Model (.C r hr) K) =
      Nat.card K ^ (r ^ 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (2 * (d + 1)) - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have h := selectedWeightCompanion_card_eq_model_mul_center (.C r hr) K
  rw [selectedWeightCompanion_C_card, selectedWeightCompanion_C_center_card] at h
  simpa only [Nat.card_eq_fintype_card (α := K), mul_comm] using h.symm

theorem model_B_card (r : ℕ) (hr : 2 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (Model (.B r hr) K) =
      (Nat.card K ^ (r ^ 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (2 * (d + 1)) - 1)) /
          Nat.gcd 2 (Nat.card K - 1) := by
  have h := model_B_centerFactor_mul_card r hr K
  have hd : 0 < Nat.gcd 2 (Nat.card K - 1) :=
    Nat.gcd_pos_of_pos_left _ (by decide)
  rw [← h, Nat.mul_div_cancel_left _ hd]

theorem model_C_card (r : ℕ) (hr : 2 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (Model (.C r hr) K) =
      (Nat.card K ^ (r ^ 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (2 * (d + 1)) - 1)) /
          Nat.gcd 2 (Nat.card K - 1) := by
  have h := model_C_centerFactor_mul_card r hr K
  have hd : 0 < Nat.gcd 2 (Nat.card K - 1) :=
    Nat.gcd_pos_of_pos_left _ (by decide)
  rw [← h, Nat.mul_div_cancel_left _ hd]

end Atlas.Chevalley

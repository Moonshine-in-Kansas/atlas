import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionDOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterCounts

/-! Exact orders of the actual adjoint type-D models. The denominator comes
from the independently proved full center of the selected companion. No old
orthogonal-group order, comparison isomorphism, or simplicity is used. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_D_centerFactor_mul_card (r : ℕ) (hr : 4 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.gcd 4 (Nat.card K ^ r - 1) * Nat.card (Model (.D r hr) K) =
      Nat.card K ^ (r * (r - 1)) * (Nat.card K ^ r - 1) *
        ∏ d ∈ Finset.range (r - 1), (Nat.card K ^ (2 * (d + 1)) - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have h := selectedWeightCompanion_card_eq_model_mul_center (.D r hr) K
  rw [selectedWeightCompanion_D_card, selectedWeightCompanion_D_center_card] at h
  simpa only [Nat.card_eq_fintype_card (α := K), mul_comm] using h.symm

theorem model_D_card (r : ℕ) (hr : 4 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (Model (.D r hr) K) =
      (Nat.card K ^ (r * (r - 1)) * (Nat.card K ^ r - 1) *
        ∏ d ∈ Finset.range (r - 1), (Nat.card K ^ (2 * (d + 1)) - 1)) /
          Nat.gcd 4 (Nat.card K ^ r - 1) := by
  have h := model_D_centerFactor_mul_card r hr K
  have hd : 0 < Nat.gcd 4 (Nat.card K ^ r - 1) :=
    Nat.gcd_pos_of_pos_left _ (by decide)
  rw [← h, Nat.mul_div_cancel_left _ hd]

end Atlas.Chevalley

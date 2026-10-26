import Atlas.LinearGroups.Chevalley.RootData.ClassicalDPoincareNumerator
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionBruhatOrder

/-! Exact order of the actual selected type-D companion in every finite
characteristic, derived from its constructed Bruhat cells and actual Weyl sum.
This statement neither uses nor identifies any older orthogonal model. -/
noncomputable section
namespace Atlas.Chevalley
open Classical ClassicalData RootData

theorem selectedWeightCompanion_D_card (r : ℕ) (hr : 4 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion (.D r hr) K) =
      Nat.card K ^ (r * (r - 1)) * (Nat.card K ^ r - 1) *
        ∏ d ∈ Finset.range (r - 1), (Nat.card K ^ (2 * (d + 1)) - 1) := by
  cases r with
  | zero => omega
  | succ s =>
    cases s with
    | zero => omega
    | succ n =>
      have h := selectedWeightCompanion_card_eq_weylSum (.D (n + 2) hr) K
      change Nat.card (SelectedWeightCompanion (.D (n + 2) hr) K) =
        Nat.card K ^ ((n + 2) * (n + 1)) * (Nat.card K - 1) ^ (n + 2) *
          rootWeylPoincareEval (pairingD (n + 2)) (baseD n) (Nat.card K) at h
      have hq : 1 ≤ Nat.card K := Nat.card_pos
      rw [mul_assoc, ClassicalDParabolic.rootWeylPoincareEval_D_product_mul n _ hq] at h
      simpa only [Nat.add_sub_cancel, mul_assoc] using h

end Atlas.Chevalley

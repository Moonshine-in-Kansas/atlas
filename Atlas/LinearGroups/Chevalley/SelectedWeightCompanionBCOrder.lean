import Atlas.LinearGroups.Chevalley.RootData.ClassicalBCPoincareNumerator
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionBruhatOrder

/-! Explicit orders of the actual selected type-B and type-C companions.
The rank is unbounded and every finite field is included. No older classical
group construction, group isomorphism, center quotient or simplicity is used. -/
noncomputable section
namespace Atlas.Chevalley
open Classical RootData ClassicalData

theorem selectedWeightCompanion_B_card (r : ℕ) (hr : 2 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion (.B r hr) K) =
      Nat.card K ^ (r ^ 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (2 * (d + 1)) - 1) := by
  cases r with
  | zero => omega
  | succ n =>
    have h := selectedWeightCompanion_card_eq_weylSum (.B (n + 1) hr) K
    change Nat.card (SelectedWeightCompanion (.B (n + 1) hr) K) =
      Nat.card K ^ ((n + 1) ^ 2) * (Nat.card K - 1) ^ (n + 1) *
        rootWeylPoincareEval (pairingB (n + 1)) (baseB n) (Nat.card K) at h
    have hq : 1 ≤ Nat.card K := Nat.card_pos
    rw [mul_assoc, ClassicalBParabolic.rootWeylPoincareEval_B_product_mul n _ hq] at h
    exact h

theorem selectedWeightCompanion_C_card (r : ℕ) (hr : 2 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion (.C r hr) K) =
      Nat.card K ^ (r ^ 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (2 * (d + 1)) - 1) := by
  cases r with
  | zero => omega
  | succ n =>
    have h := selectedWeightCompanion_card_eq_weylSum (.C (n + 1) hr) K
    change Nat.card (SelectedWeightCompanion (.C (n + 1) hr) K) =
      Nat.card K ^ ((n + 1) ^ 2) * (Nat.card K - 1) ^ (n + 1) *
        rootWeylPoincareEval (pairingC (n + 1)) (baseC n) (Nat.card K) at h
    have hq : 1 ≤ Nat.card K := Nat.card_pos
    rw [mul_assoc, ClassicalBParabolic.rootWeylPoincareEval_C_product_mul n _ hq] at h
    exact h

end Atlas.Chevalley

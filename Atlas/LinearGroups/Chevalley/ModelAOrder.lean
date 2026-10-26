import Atlas.LinearGroups.Chevalley.RootData.TypeAPoincareProduct
import Atlas.LinearGroups.Chevalley.ModelBruhatOrder

/-! Explicit orders of the actual uniform-engine type-A selected companion and
adjoint model. The rank remains a variable, and every finite field is included.
The quotient factor is the independently proved full-cover center cardinality. -/
noncomputable section
namespace Atlas.Chevalley
open RootData

theorem selectedWeightCompanion_A_card (r : ℕ) (hr : 1 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion (.A r hr) K) =
      Nat.card K ^ (r * (r + 1) / 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (d + 2) - 1) := by
  have h := selectedWeightCompanion_card_eq_weylSum (.A r hr) K
  change Nat.card (SelectedWeightCompanion (.A r hr) K) =
    Nat.card K ^ (r * (r + 1) / 2) * (Nat.card K - 1) ^ r *
      rootWeylPoincareEval (TypeAData.pairing (r + 1)) (TypeAData.base r)
        (Nat.card K) at h
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [mul_assoc, TypeAData.rootWeylPoincareEval_A_product_mul _ _ hq] at h
  exact h

theorem model_A_centerFactor_mul_card (r : ℕ) (hr : 1 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.gcd (r + 1) (Nat.card K - 1) * Nat.card (Model (.A r hr) K) =
      Nat.card K ^ (r * (r + 1) / 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (d + 2) - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have h := model_centerFactor_mul_card_eq_weylSum (.A r hr) K
  change Nat.gcd (r + 1) (Fintype.card K - 1) * Nat.card (Model (.A r hr) K) =
    Fintype.card K ^ (r * (r + 1) / 2) * (Fintype.card K - 1) ^ r *
      rootWeylPoincareEval (TypeAData.pairing (r + 1)) (TypeAData.base r)
        (Fintype.card K) at h
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [mul_assoc, TypeAData.rootWeylPoincareEval_A_product_mul _ _ hq] at h
  simpa only [Nat.card_eq_fintype_card (α := K)] using h

theorem model_A_card (r : ℕ) (hr : 1 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (Model (.A r hr) K) =
      (Nat.card K ^ (r * (r + 1) / 2) *
        ∏ d ∈ Finset.range r, (Nat.card K ^ (d + 2) - 1)) /
          Nat.gcd (r + 1) (Nat.card K - 1) := by
  have h := model_A_centerFactor_mul_card r hr K
  have hd : 0 < Nat.gcd (r + 1) (Nat.card K - 1) :=
    Nat.gcd_pos_of_pos_left _ (Nat.succ_pos r)
  rw [← h, Nat.mul_div_cancel_left _ hd]

end Atlas.Chevalley

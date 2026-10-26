import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionDegreeOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterCounts

/-! The degree-list order of the actual adjoint model. The multiplier is the
proved full center of the actual companion. Divisibility and positivity precede
the natural-number division formula. This is an uncompiled source candidate. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_centerFactor_mul_card_eq_orderPolynomial
    (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    Φ.centerFactor (Nat.card K) * Nat.card (Model Φ K) =
      Φ.orderPolynomial (Nat.card K) := by
  let : Fintype K := Fintype.ofFinite K
  have h := selectedWeightCompanion_card_eq_model_mul_center Φ K
  rw [selectedWeightCompanion_card_eq_orderPolynomial,
    selectedWeightCompanion_center_card] at h
  simpa only [Nat.card_eq_fintype_card (α := K), mul_comm] using h.symm

theorem model_centerFactor_pos
    (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    0 < Φ.centerFactor (Nat.card K) := by
  let : Fintype K := Fintype.ofFinite K
  have h := selectedWeightCompanion_center_card Φ K
  rw [← Nat.card_eq_fintype_card (α := K)] at h
  rw [← h]
  exact Nat.card_pos

theorem model_centerFactor_dvd_orderPolynomial
    (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    Φ.centerFactor (Nat.card K) ∣ Φ.orderPolynomial (Nat.card K) :=
  ⟨Nat.card (Model Φ K),
    (model_centerFactor_mul_card_eq_orderPolynomial Φ K).symm⟩

theorem model_card_eq_orderPolynomial_div_centerFactor
    (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    Nat.card (Model Φ K) =
      Φ.orderPolynomial (Nat.card K) / Φ.centerFactor (Nat.card K) := by
  rw [← model_centerFactor_mul_card_eq_orderPolynomial Φ K]
  exact (Nat.mul_div_cancel_left _ (model_centerFactor_pos Φ K)).symm

end Atlas.Chevalley

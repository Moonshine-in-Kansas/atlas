import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionBruhatOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterCounts

/-! The actual adjoint model's order, multiplied by its proved cover-center
factor, is the Weyl length sum. No degree-product evaluation is assumed. -/
noncomputable section
namespace Atlas.Chevalley
open Classical RootData

theorem model_centerFactor_mul_card_eq_weylSum (Φ : RootType)
    (K : Type*) [Field K] [Fintype K] :
    Φ.centerFactor (Fintype.card K) * Nat.card (Model Φ K) =
      Fintype.card K ^ Φ.positiveRootNumber * (Fintype.card K - 1) ^ Φ.rank *
        rootWeylPoincareEval (rootDatum Φ).pairing (rootDatum Φ).base
          (Fintype.card K) := by
  have h := selectedWeightCompanion_card_eq_model_mul_center Φ K
  rw [selectedWeightCompanion_center_card, selectedWeightCompanion_card_eq_weylSum,
    Nat.card_eq_fintype_card] at h
  simpa only [mul_comm (Nat.card (Model Φ K))] using h.symm

theorem model_centerFactor_dvd_weylSum (Φ : RootType)
    (K : Type*) [Field K] [Fintype K] :
    Φ.centerFactor (Fintype.card K) ∣
      Fintype.card K ^ Φ.positiveRootNumber * (Fintype.card K - 1) ^ Φ.rank *
        rootWeylPoincareEval (rootDatum Φ).pairing (rootDatum Φ).base
          (Fintype.card K) :=
  ⟨Nat.card (Model Φ K), (model_centerFactor_mul_card_eq_weylSum Φ K).symm⟩

end Atlas.Chevalley

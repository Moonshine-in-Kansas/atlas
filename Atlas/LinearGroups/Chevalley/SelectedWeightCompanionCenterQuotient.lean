import Atlas.LinearGroups.Chevalley.WeightCompanionCenterCharacters
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion

/-! Actual selected-family adapters. The verified root-data dispatcher supplies
simple diamonds and the selected weights supply the full weight-span condition.
No good-range, order-recognition or simplicity premise is introduced. -/
noncomputable section
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable (Φ : RootType) (K : Type*) [Field K] [Finite K]

theorem selectedWeightCompanion_center_eq_rhoKernel :
    Subgroup.center (SelectedWeightCompanion Φ K) =
      (selectedWeightCompanionRho Φ K).ker :=
  weightCompanion_center_eq_rhoKernel_finiteField
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ)

def selectedWeightCompanionCenterQuotientAdjointEquiv :
    SelectedWeightCompanion Φ K ⧸ Subgroup.center (SelectedWeightCompanion Φ K) ≃*
      Model Φ K :=
  weightCompanionCenterQuotientAdjointEquiv
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ)

def selectedWeightCompanionCenterCharacterEquiv :
    Subgroup.center (SelectedWeightCompanion Φ K) ≃*
      (Multiplicative (WeightLattice (rootDatum Φ).pairing ⧸
        rootLattice (rootDatum Φ).pairing) →* Kˣ) :=
  weightCompanionCenterCharacterEquiv
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ) (selectedWeightSet_spans Φ)

theorem selectedWeightCompanion_center_card_eq_character :
    Nat.card (Subgroup.center (SelectedWeightCompanion Φ K)) =
      Nat.card (Multiplicative (WeightLattice (rootDatum Φ).pairing ⧸
        rootLattice (rootDatum Φ).pairing) →* Kˣ) :=
  Nat.card_congr (selectedWeightCompanionCenterCharacterEquiv Φ K).toEquiv

theorem selectedWeightCompanion_card_eq_model_mul_center :
    Nat.card (SelectedWeightCompanion Φ K) =
      Nat.card (Model Φ K) * Nat.card (Subgroup.center (SelectedWeightCompanion Φ K)) :=
  weightCompanion_card_eq_adjoint_mul_center
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ)

end Atlas.Chevalley

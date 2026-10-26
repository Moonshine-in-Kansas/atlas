import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionTorus
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusOrder
/-! Actual selected-model torus order, uniformly for all nine types. -/
noncomputable section
namespace Atlas.Chevalley

def selectedWeightCompanionTorusSubgroup (Φ : RootType) (R : Type*) [CommRing R] :
    Subgroup (SelectedWeightCompanion Φ R) :=
  weightCompanionTorusSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

theorem selectedWeightCompanionTorus_card (Φ : RootType) (K : Type*) [Field K] [Fintype K] :
    Nat.card (selectedWeightCompanionTorusSubgroup Φ K) = (Fintype.card K - 1) ^ Φ.rank := by
  have h := weightCompanionTorus_card_finiteField (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (selectedWeightSet_spans Φ)
  simpa only [selectedWeightCompanionTorusSubgroup,model_base_card] using h
end Atlas.Chevalley

import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusFaithful

/-! Actual faithful torus parameters for all nine selected-weight models. -/
noncomputable section
namespace Atlas.Chevalley

def selectedWeightCompanionTorusParameters (Φ : RootType) (R : Type*) [CommRing R] :
    ((rootDatum Φ).base.support → Rˣ) →* SelectedWeightCompanion Φ R :=
  weightCompanionTorusParameters (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

theorem selectedWeightCompanionTorusParameters_injective (Φ : RootType) (R : Type*) [CommRing R] :
    Function.Injective (selectedWeightCompanionTorusParameters Φ R) :=
  weightCompanionTorusParameters_injective_of_span (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R
    (selectedWeightSet_spans Φ)

end Atlas.Chevalley

import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidA2
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion

/-! Source candidate: literal selected-companion A2 braid in actual numbered
simple-root coordinates, with no diamond or projection-kernel premise. -/

noncomputable section
namespace Atlas.Chevalley

theorem selectedWeightCompanionWeyl_a2_braid
    (Φ : RootType) (R : Type*) [CommRing R] (i j : Fin Φ.rank)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -1) :
    let W (k : Fin Φ.rank) := selectedWeightCompanionX Φ R k 1 *
      selectedWeightCompanionY Φ R k (-1) * selectedWeightCompanionX Φ R k 1
    W i * W j * W i = W j * W i * W j := by
  exact weightCompanionWeyl_a2_braid
    (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R
    ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) hij hji

end Atlas.Chevalley

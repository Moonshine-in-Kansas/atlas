import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidDihedral
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion

/-! Length-four and length-six braid identities for the actual selected
companion generators in the numbered simple-root coordinates. -/

noncomputable section
namespace Atlas.Chevalley

theorem selectedWeightCompanionWeyl_b2_braid
    (Φ : RootType) (R : Type*) [CommRing R] (i j : Fin Φ.rank)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -2) :
    let W (k : Fin Φ.rank) := selectedWeightCompanionX Φ R k 1 *
      selectedWeightCompanionY Φ R k (-1) * selectedWeightCompanionX Φ R k 1
    W i * W j * W i * W j = W j * W i * W j * W i := by
  exact weightCompanionWeyl_b2_braid
    (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R
    ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) hij hji

theorem selectedWeightCompanionWeyl_g2_braid
    (Φ : RootType) (R : Type*) [CommRing R] (i j : Fin Φ.rank)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -3) :
    let W (k : Fin Φ.rank) := selectedWeightCompanionX Φ R k 1 *
      selectedWeightCompanionY Φ R k (-1) * selectedWeightCompanionX Φ R k 1
    W i * W j * W i * W j * W i * W j = W j * W i * W j * W i * W j * W i := by
  exact weightCompanionWeyl_g2_braid
    (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R
    ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) hij hji

end Atlas.Chevalley

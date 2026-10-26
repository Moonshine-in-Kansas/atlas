import Atlas.LinearGroups.Chevalley.WeightCompanionDoubleEdgeCommutator
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion

/-! Actual numbered-root double-edge identities for the selected companion.
The root-data dispatcher proves the generic diamond input; each selected
weight orbit is the existing reflection-closed minuscule orbit. -/

noncomputable section
namespace Atlas.Chevalley
open scoped commutatorElement

variable (Φ : RootType) (R : Type*) [CommRing R]

theorem selectedWeightCompanionX_b2_commutator_eq_weyl_product
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -2) (s t : R) :
    let W (k : Fin Φ.rank) := selectedWeightCompanionX Φ R k 1 *
      selectedWeightCompanionY Φ R k (-1) * selectedWeightCompanionX Φ R k 1
    ⁅selectedWeightCompanionX Φ R i s, selectedWeightCompanionX Φ R j t⁆ =
      (W j * selectedWeightCompanionX Φ R i (-s * t) * (W j)⁻¹) *
      (W i * selectedWeightCompanionX Φ R j (s ^ 2 * t) * (W i)⁻¹) := by
  exact weightCompanionX_b2_commutator_eq_weyl_product
    (rootDatum Φ).pairing (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ)
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R
    ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j)
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hij hji s t

theorem selectedWeightCompanionY_b2_commutator_eq_negative_weyl_product
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -2) (s t : R) :
    let V (k : Fin Φ.rank) := selectedWeightCompanionY Φ R k 1 *
      selectedWeightCompanionX Φ R k (-1) * selectedWeightCompanionY Φ R k 1
    ⁅selectedWeightCompanionY Φ R i s, selectedWeightCompanionY Φ R j t⁆ =
      (V j * selectedWeightCompanionY Φ R i (-s * t) * (V j)⁻¹) *
      (V i * selectedWeightCompanionY Φ R j (s ^ 2 * t) * (V i)⁻¹) := by
  exact weightCompanionY_b2_commutator_eq_negative_weyl_product
    (rootDatum Φ).pairing (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ)
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R
    ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j)
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hij hji s t

end Atlas.Chevalley

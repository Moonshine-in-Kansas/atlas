import Atlas.LinearGroups.Chevalley.WeightCompanionPerfectnessA2
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion

/-! Numbered-root interfaces for the actual selected-weight construction.
The actual root-data dispatcher discharges the generic diamond condition. -/

noncomputable section
namespace Atlas.Chevalley
open Group
open scoped commutatorElement

variable (Φ : RootType) (R : Type*) [CommRing R]

theorem selectedWeightCompanionX_a2_commutator_eq_weyl_conjugate
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -1) (s t : R) :
    let W := selectedWeightCompanionX Φ R i 1 * selectedWeightCompanionY Φ R i (-1) *
      selectedWeightCompanionX Φ R i 1
    ⁅selectedWeightCompanionX Φ R i s, selectedWeightCompanionX Φ R j t⁆ =
      W * selectedWeightCompanionX Φ R j (s * t) * W⁻¹ := by
  exact weightCompanionX_a2_commutator_eq_weyl_conjugate
    (rootDatum Φ).pairing (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ)
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R
    ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j)
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hij hji s t

theorem selectedWeightCompanionY_a2_commutator_eq_negative_weyl_conjugate
    (i j : Fin Φ.rank) (hne : i ≠ j)
    (hij : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1)
    (hji : (rootDatum Φ).base.cartanMatrix
      ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -1) (s t : R) :
    let V := selectedWeightCompanionY Φ R i 1 * selectedWeightCompanionX Φ R i (-1) *
      selectedWeightCompanionY Φ R i 1
    ⁅selectedWeightCompanionY Φ R i s, selectedWeightCompanionY Φ R j t⁆ =
      V * selectedWeightCompanionY Φ R j (s * t) * V⁻¹ := by
  exact weightCompanionY_a2_commutator_eq_negative_weyl_conjugate
    (rootDatum Φ).pairing (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ)
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R
    ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j)
    (fun h => hne ((rootDatum Φ).indexEquiv.injective h)) hij hji s t

/-- Perfectness for the selected simultaneous model, with the only remaining
combinatorial input stated on its actual numbered Cartan matrix. -/
theorem selectedWeightCompanion_isPerfect_of_a2_neighbours
    (hrows : ∀ i : Fin Φ.rank, ∃ j : Fin Φ.rank, j ≠ i ∧
      (rootDatum Φ).base.cartanMatrix
        ((rootDatum Φ).indexEquiv i) ((rootDatum Φ).indexEquiv j) = -1 ∧
      (rootDatum Φ).base.cartanMatrix
        ((rootDatum Φ).indexEquiv j) ((rootDatum Φ).indexEquiv i) = -1) :
    IsPerfect (SelectedWeightCompanion Φ R) := by
  apply weightCompanion_isPerfect_of_a2_neighbours
    (rootDatum Φ).pairing (rootDatum Φ).base (rootDatum_simpleDiamondProducts Φ)
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R
  intro a
  obtain ⟨i, rfl⟩ := (rootDatum Φ).indexEquiv.surjective a
  obtain ⟨j, hne, hij, hji⟩ := hrows i
  exact ⟨(rootDatum Φ).indexEquiv j,
    fun h => hne ((rootDatum Φ).indexEquiv.injective h), hij, hji⟩

end Atlas.Chevalley

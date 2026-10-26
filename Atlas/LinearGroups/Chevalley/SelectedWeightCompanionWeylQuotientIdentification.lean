import Atlas.LinearGroups.Chevalley.WeightCompanionWeylQuotientIdentification
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion

/-! All actual selected root types satisfy the generic diamond premise.
Consequently their literal torus quotients have faithful root-label actions
and are isomorphic to their actual root-permutation Weyl images. -/

noncomputable section
namespace Atlas.Chevalley
open Classical

variable (Φ : RootType) (R : Type*) [CommRing R] [Nontrivial R]




local instance selectedQuotientIdentificationTorusNormal : Subgroup.Normal ((Subgroup.subgroupOf (weightCompanionTorusSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R) (weightCompanionExtendedWeylSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R))) :=
  weightCompanionTorusSubgroup_normal_extendedWeyl
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

/-- No unproved diamond premise remains for any actual selected root type. -/
theorem selectedWeightCompanionWeylQuotientAction_injective :
    Function.Injective
      (weightCompanionWeylQuotientAction (rootDatum Φ).pairing (rootDatum Φ).base
        (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
        (selectedWeightOrbits_minuscule Φ) R) :=
  weightCompanionWeylQuotientAction_injective
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R
    (rootDatum_simpleDiamondProducts Φ)

/-- The actual selected normalizer's root-action kernel is exactly its torus. -/
theorem selectedWeightCompanionNRootPermHom_ker_eq_torus :
    (weightCompanionNRootPermHom (rootDatum Φ).pairing (rootDatum Φ).base
      (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
      (selectedWeightOrbits_minuscule Φ) R).ker = ((Subgroup.subgroupOf (weightCompanionTorusSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R) (weightCompanionExtendedWeylSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R))) :=
  weightCompanionNRootPermHom_ker_eq_torus
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R
    (rootDatum_simpleDiamondProducts Φ)

/-- The actual selected model's literal N/T, over every nontrivial commutative
ring, is isomorphic to the actual integral root-permutation Weyl image. -/
def selectedWeightCompanionWeylQuotientEquiv :
    ((weightCompanionExtendedWeylSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R) ⧸ ((Subgroup.subgroupOf (weightCompanionTorusSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R) (weightCompanionExtendedWeylSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) R)))) ≃* (rootDatum Φ).pairing.weylGroupToPerm.range :=
  weightCompanionWeylQuotientEquiv
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R
    (rootDatum_simpleDiamondProducts Φ)

/-- In the existing numbered simple-root coordinates, the isomorphism sends
the actual simple Weyl coset to the corresponding actual root reflection. -/
theorem selectedWeightCompanionWeylQuotientEquiv_simple (i : Fin Φ.rank) :
    selectedWeightCompanionWeylQuotientEquiv Φ R
      (weightCompanionSimpleWeylCoset (rootDatum Φ).pairing (rootDatum Φ).base
        (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
        (selectedWeightOrbits_minuscule Φ) R ((rootDatum Φ).indexEquiv i)) =
      RootData.simpleWeylReflection (rootDatum Φ).pairing (rootDatum Φ).base
        ((rootDatum Φ).indexEquiv i) := by
  exact weightCompanionWeylQuotientFullAction_simple
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R
    ((rootDatum Φ).indexEquiv i)

end Atlas.Chevalley

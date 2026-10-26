import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionTorusOrder
import Atlas.LinearGroups.Chevalley.RootData.PositiveRootCounts

/-! Uniform positive-subgroup and U*T counts for all nine actual selected
root-operator models. The simple-diamond premise is discharged by the existing
coordinate providers. These are subgroup orders, not full-group orders. -/
noncomputable section
namespace Atlas.Chevalley
open Classical

def selectedWeightCompanionPositiveSubgroup (Φ : RootType)
    (R : Type*) [CommRing R] [Nontrivial R] : Subgroup (SelectedWeightCompanion Φ R) :=
  positiveWitnessedWeightCompanionSubgroup (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

theorem selectedWeightCompanionPositive_card (Φ : RootType)
    (R : Type*) [CommRing R] [Nontrivial R] [Finite R] :
    Nat.card (selectedWeightCompanionPositiveSubgroup Φ R) =
      Nat.card R ^ Φ.positiveRootNumber := by
  have h := positiveWitnessedWeightCompanionSubgroup_card
    (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ)
    R (rootDatum_simpleDiamondProducts Φ)
  simpa only [selectedWeightCompanionPositiveSubgroup, rootDatum_positive_root_card] using h

theorem selectedWeightCompanionPositive_card_finiteField (Φ : RootType)
    (K : Type*) [Field K] [Fintype K] :
    Nat.card (selectedWeightCompanionPositiveSubgroup Φ K) =
      Fintype.card K ^ Φ.positiveRootNumber := by
  rw [selectedWeightCompanionPositive_card, Nat.card_eq_fintype_card]

def selectedWeightCompanionPositiveTorusJoin (Φ : RootType)
    (R : Type*) [CommRing R] [Nontrivial R] : Subgroup (SelectedWeightCompanion Φ R) :=
  positiveWitnessedTorusJoin (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) R

theorem selectedWeightCompanionPositiveTorusJoin_card (Φ : RootType)
    (K : Type*) [Field K] [Fintype K] :
    Nat.card (selectedWeightCompanionPositiveTorusJoin Φ K) =
      Fintype.card K ^ Φ.positiveRootNumber * (Fintype.card K - 1) ^ Φ.rank := by
  have h := positiveWitnessedTorusJoin_card
    (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ)
    K (rootDatum_simpleDiamondProducts Φ)
  change Nat.card (selectedWeightCompanionPositiveTorusJoin Φ K) =
    Nat.card K ^ Nat.card {β : (rootDatum Φ).Root // (rootDatum Φ).base.IsPos β} *
      Nat.card (selectedWeightCompanionTorusSubgroup Φ K) at h
  rw [rootDatum_positive_root_card, selectedWeightCompanionTorus_card] at h
  have hK : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  simpa only [hK] using h

end Atlas.Chevalley

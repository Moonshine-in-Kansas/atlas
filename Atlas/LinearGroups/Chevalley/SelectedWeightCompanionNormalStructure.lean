import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalDichotomy
import Atlas.LinearGroups.Chevalley.RootData.CartanConnectivity
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionPerfectnessGood
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusSolvable
import Atlas.GroupTheory.PerfectSolvableSupplement

/-! The actual selected companion has only central proper normal subgroups
in the existing good finite-field range. It is not asserted to be simple:
its previously determined full center is retained. -/
noncomputable section
namespace Atlas.Chevalley

theorem selectedWeightCompanion_normal_le_center_or_positiveJoin_sup_eq_top
    (Φ : RootType) (K : Type*) [Field K]
    (A : Subgroup (SelectedWeightCompanion Φ K)) [A.Normal] :
    A ≤ Subgroup.center (SelectedWeightCompanion Φ K) ∨
      A ⊔ positiveWitnessedTorusJoin (rootDatum Φ).pairing (rootDatum Φ).base
        (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
        (selectedWeightOrbits_minuscule Φ) K = ⊤ :=
  weightCompanion_normal_le_center_or_positiveJoin_sup_eq_top
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ) (rootDatum_cartan_connected Φ) A

theorem selectedWeightCompanion_normal_le_center_or_eq_top_of_good
    (Φ : RootType) (K : Type*) [Field K] [Fintype K]
    (hgood : Φ.Good (Fintype.card K))
    (A : Subgroup (SelectedWeightCompanion Φ K)) [A.Normal] :
    A ≤ Subgroup.center (SelectedWeightCompanion Φ K) ∨ A = ⊤ := by
  let B := positiveWitnessedTorusJoin (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) K
  letI := selectedWeightCompanion_isPerfect_of_good Φ K hgood
  letI : Group.IsSolvable B := positiveWitnessedTorusJoin_isSolvable
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ)
  rcases selectedWeightCompanion_normal_le_center_or_positiveJoin_sup_eq_top Φ K A with h | h
  · exact Or.inl h
  · exact Or.inr (Atlas.GroupTheory.eq_top_of_perfect_normal_solvable_sup A B h)

end Atlas.Chevalley

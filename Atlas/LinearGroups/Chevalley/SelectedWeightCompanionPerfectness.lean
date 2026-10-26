import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Atlas.LinearGroups.Chevalley.WeightCompanionPerfectness

/-! Perfectness of the actual deterministic all-type companion.
No central-kernel or simply-connected identification is assumed. -/
noncomputable section
namespace Atlas.Chevalley
open Group

theorem selectedWeightCompanion_isPerfect_of_unit
    (Φ : RootType) (K : Type*) [Field K] (a : Kˣ) (ha : (a : K)^2 ≠ 1) :
    IsPerfect (SelectedWeightCompanion Φ K) :=
  weightCompanion_isPerfect_of_unit (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) K a ha

theorem selectedWeightCompanion_isPerfect_of_card_gt_three
    (Φ : RootType) (K : Type*) [Field K] [Fintype K] (hq : 3 < Fintype.card K) :
    IsPerfect (SelectedWeightCompanion Φ K) :=
  weightCompanion_isPerfect_of_card_gt_three (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) K hq

end Atlas.Chevalley

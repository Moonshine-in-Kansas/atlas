import Atlas.LinearGroups.Chevalley.WeightCompanionPerfectnessDoubleEdge
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Atlas.LinearGroups.Chevalley.RootData.DoubleEdgeCoverBC

/-! All-ring perfectness of the actual selected-weight B/C companions in
rank at least three. The actual root-data and coordinate Cartan cover discharge
the generic assumptions. No old classical group model or kernel theorem is used. -/

noncomputable section
namespace Atlas.Chevalley
open Group

/-- Actual type B selected companion, in every coefficient characteristic. -/
theorem selectedWeightCompanion_B_isPerfect_of_rank_ge_three
    (r : ℕ) (hr : 3 ≤ r) (R : Type*) [CommRing R] :
    IsPerfect (SelectedWeightCompanion (.B r (by omega)) R) := by
  apply weightCompanion_isPerfect_of_a2_double_cover
    (rootDatum (.B r (by omega))).pairing (rootDatum (.B r (by omega))).base
    (rootDatum_simpleDiamondProducts (.B r (by omega)))
    (selectedWeightOrbits (.B r (by omega)))
    (selectedWeightOrbits_closed (.B r (by omega)))
    (selectedWeightOrbits_minuscule (.B r (by omega))) R
  with_unfolding_all exact B_base_a2_double_cover (r - 1) (by omega)

/-- Actual type C selected companion, in every coefficient characteristic. -/
theorem selectedWeightCompanion_C_isPerfect_of_rank_ge_three
    (r : ℕ) (hr : 3 ≤ r) (R : Type*) [CommRing R] :
    IsPerfect (SelectedWeightCompanion (.C r (by omega)) R) := by
  apply weightCompanion_isPerfect_of_a2_double_cover
    (rootDatum (.C r (by omega))).pairing (rootDatum (.C r (by omega))).base
    (rootDatum_simpleDiamondProducts (.C r (by omega)))
    (selectedWeightOrbits (.C r (by omega)))
    (selectedWeightOrbits_closed (.C r (by omega)))
    (selectedWeightOrbits_minuscule (.C r (by omega))) R
  with_unfolding_all exact C_base_a2_double_cover (r - 1) (by omega)

end Atlas.Chevalley

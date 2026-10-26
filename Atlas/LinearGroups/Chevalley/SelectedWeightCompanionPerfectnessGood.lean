import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionPerfectnessADEF
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionPerfectnessBC
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.B2CompanionPerfectness
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2CompanionPerfectness
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionPerfectnessOdd
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionPerfectness

/-! Uniform good-range perfectness of the actual selected-weight companion.
Each branch uses a proof on the actual simultaneous representation. No
perfectness conclusion is lifted through the adjoint projection. -/

namespace Atlas.Chevalley
open Group

theorem selectedWeightCompanion_isPerfect_of_good
    (Φ : RootType) (K : Type*) [Field K] [Fintype K]
    (hgood : Φ.Good (Fintype.card K)) :
    IsPerfect (SelectedWeightCompanion Φ K) := by
  cases Φ with
  | A r hr =>
      change 2 ≤ Fintype.card K ∧
        (r ≠ 1 ∨ (Fintype.card K ≠ 2 ∧ Fintype.card K ≠ 3)) at hgood
      by_cases hsmall : r = 1
      · exact selectedWeightCompanion_isPerfect_of_card_gt_three (.A r hr) K (by omega)
      · exact selectedWeightCompanion_A_isPerfect_of_rank_ge_two r (by omega) K
  | B r hr =>
      change 2 ≤ Fintype.card K ∧ (r ≠ 2 ∨ Fintype.card K ≠ 2) at hgood
      by_cases hsmall : r = 2
      · subst r
        exact selectedWeightCompanion_B2_isPerfect_of_card_gt_two K (by omega)
      · exact selectedWeightCompanion_B_isPerfect_of_rank_ge_three r (by omega) K
  | C r hr =>
      change 2 ≤ Fintype.card K ∧ (r ≠ 2 ∨ Fintype.card K ≠ 2) at hgood
      by_cases hsmall : r = 2
      · subst r
        exact selectedWeightCompanion_C2_isPerfect_of_card_gt_two K (by omega)
      · exact selectedWeightCompanion_C_isPerfect_of_rank_ge_three r (by omega) K
  | D r hr => exact selectedWeightCompanion_D_isPerfect_of_rank_ge_four r hr K
  | E6 => exact selectedWeightCompanion_E6_isPerfect K
  | E7 => exact selectedWeightCompanion_E7_isPerfect K
  | E8 => exact selectedWeightCompanion_E8_isPerfect K
  | F4 => exact selectedWeightCompanion_F4_isPerfect K
  | G2 =>
      change 2 ≤ Fintype.card K ∧ Fintype.card K ≠ 2 at hgood
      by_cases hlarge : 3 < Fintype.card K
      · exact selectedWeightCompanion_isPerfect_of_card_gt_three .G2 K hlarge
      · exact selectedWeightCompanion_G2_isPerfect_of_card_three K (by omega)

end Atlas.Chevalley

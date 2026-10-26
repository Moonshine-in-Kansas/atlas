import Atlas.LinearGroups.Chevalley.ModelPerfectnessA2DEF
import Atlas.LinearGroups.Chevalley.ModelPerfectnessDoubleEdgeBC
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.B2Perfectness
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2PerfectnessFinite
import Atlas.LinearGroups.Chevalley.ModelPerfectnessOdd
import Atlas.LinearGroups.Chevalley.AdjointPerfectness

/-! Uniform good-range perfectness of the actual adjoint model. The parameter
predicate is the existing RootType.Good; this is a sufficient-range theorem,
not a converse, a simplicity theorem, or an earlier-model identification. -/

namespace Atlas.Chevalley
open Group

theorem model_isPerfect_of_good (Φ : RootType) (K : Type*) [Field K] [Fintype K]
    (hgood : Φ.Good (Fintype.card K)) : IsPerfect (Model Φ K) := by
  cases Φ with
  | A r hr =>
      change 2 ≤ Fintype.card K ∧
        (r ≠ 1 ∨ (Fintype.card K ≠ 2 ∧ Fintype.card K ≠ 3)) at hgood
      by_cases hsmall : r = 1
      · exact model_isPerfect_of_card_gt_three K (.A r hr) (by omega)
      · exact model_A_isPerfect_of_rank_ge_two r (by omega) K
  | B r hr =>
      change 2 ≤ Fintype.card K ∧ (r ≠ 2 ∨ Fintype.card K ≠ 2) at hgood
      by_cases hsmall : r = 2
      · subst r
        exact model_B2_isPerfect_of_card_gt_two K (by omega)
      · exact model_B_isPerfect_of_rank_ge_three r (by omega) K
  | C r hr =>
      change 2 ≤ Fintype.card K ∧ (r ≠ 2 ∨ Fintype.card K ≠ 2) at hgood
      by_cases hsmall : r = 2
      · subst r
        exact model_C2_isPerfect_of_card_gt_two K (by omega)
      · exact model_C_isPerfect_of_rank_ge_three r (by omega) K
  | D r hr => exact model_D_isPerfect r hr K
  | E6 => exact model_E6_isPerfect K
  | E7 => exact model_E7_isPerfect K
  | E8 => exact model_E8_isPerfect K
  | F4 => exact model_F4_isPerfect K
  | G2 =>
      change 2 ≤ Fintype.card K ∧ Fintype.card K ≠ 2 at hgood
      by_cases hlarge : 3 < Fintype.card K
      · exact model_isPerfect_of_card_gt_three K .G2 hlarge
      · exact model_G2_isPerfect_of_card_three K (by omega)

end Atlas.Chevalley

import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralOperatorData

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.G2
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_3 :
    simpleMatrix 3 * simpleMatrix 3 = 2 • simpleSecondMatrix 3 := by
  decide +kernel

theorem simple_cube_3 :
    simpleSecondMatrix 3 * simpleMatrix 3 = 0 := by
  decide +kernel

theorem geck_square_3 :
    geckMatrix 3 * geckMatrix 3 = 2 • geckSecondMatrix 3 := by
  decide +kernel

theorem geck_cube_3 :
    geckSecondMatrix 3 * geckMatrix 3 = 3 • geckThirdMatrix 3 := by
  decide +kernel

theorem geck_fourth_3 :
    geckThirdMatrix 3 * geckMatrix 3 = 0 := by
  decide +kernel

theorem simple_commutator_3 : ∀ j : Fin 14,
    simpleMatrix 3 * basisMatrix j - basisMatrix j * simpleMatrix 3 =
      basisCombination (fun k => geckMatrix 3 k j) := by
  decide +kernel

theorem simple_second_conjugation_3 : ∀ j : Fin 14,
    simpleSecondMatrix 3 * basisMatrix j + basisMatrix j * simpleSecondMatrix 3 -
      simpleMatrix 3 * basisMatrix j * simpleMatrix 3 =
        basisCombination (fun k => geckSecondMatrix 3 k j) := by
  decide +kernel

theorem simple_third_conjugation_3 : ∀ j : Fin 14,
    simpleMatrix 3 * basisMatrix j * simpleSecondMatrix 3 -
      simpleSecondMatrix 3 * basisMatrix j * simpleMatrix 3 =
        basisCombination (fun k => geckThirdMatrix 3 k j) := by
  decide +kernel

theorem simple_fourth_conjugation_3 : ∀ j : Fin 14,
    simpleSecondMatrix 3 * basisMatrix j * simpleSecondMatrix 3 = 0 := by
  decide +kernel

end Atlas.Chevalley.Comparison.G2

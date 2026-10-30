import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralOperatorData

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.G2
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_1 :
    simpleMatrix 1 * simpleMatrix 1 = 2 • simpleSecondMatrix 1 := by
  decide +kernel

theorem simple_cube_1 :
    simpleSecondMatrix 1 * simpleMatrix 1 = 0 := by
  decide +kernel

theorem geck_square_1 :
    geckMatrix 1 * geckMatrix 1 = 2 • geckSecondMatrix 1 := by
  decide +kernel

theorem geck_cube_1 :
    geckSecondMatrix 1 * geckMatrix 1 = 3 • geckThirdMatrix 1 := by
  decide +kernel

theorem geck_fourth_1 :
    geckThirdMatrix 1 * geckMatrix 1 = 0 := by
  decide +kernel

theorem simple_commutator_1 : ∀ j : Fin 14,
    simpleMatrix 1 * basisMatrix j - basisMatrix j * simpleMatrix 1 =
      basisCombination (fun k => geckMatrix 1 k j) := by
  decide +kernel

theorem simple_second_conjugation_1 : ∀ j : Fin 14,
    simpleSecondMatrix 1 * basisMatrix j + basisMatrix j * simpleSecondMatrix 1 -
      simpleMatrix 1 * basisMatrix j * simpleMatrix 1 =
        basisCombination (fun k => geckSecondMatrix 1 k j) := by
  decide +kernel

theorem simple_third_conjugation_1 : ∀ j : Fin 14,
    simpleMatrix 1 * basisMatrix j * simpleSecondMatrix 1 -
      simpleSecondMatrix 1 * basisMatrix j * simpleMatrix 1 =
        basisCombination (fun k => geckThirdMatrix 1 k j) := by
  decide +kernel

theorem simple_fourth_conjugation_1 : ∀ j : Fin 14,
    simpleSecondMatrix 1 * basisMatrix j * simpleSecondMatrix 1 = 0 := by
  decide +kernel

end Atlas.Chevalley.Comparison.G2

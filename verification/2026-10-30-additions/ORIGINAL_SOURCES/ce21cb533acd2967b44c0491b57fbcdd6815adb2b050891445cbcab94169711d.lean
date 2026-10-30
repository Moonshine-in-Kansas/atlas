import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralOperatorData

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.G2
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_2 :
    simpleMatrix 2 * simpleMatrix 2 = 2 • simpleSecondMatrix 2 := by
  decide +kernel

theorem simple_cube_2 :
    simpleSecondMatrix 2 * simpleMatrix 2 = 0 := by
  decide +kernel

theorem geck_square_2 :
    geckMatrix 2 * geckMatrix 2 = 2 • geckSecondMatrix 2 := by
  decide +kernel

theorem geck_cube_2 :
    geckSecondMatrix 2 * geckMatrix 2 = 3 • geckThirdMatrix 2 := by
  decide +kernel

theorem geck_fourth_2 :
    geckThirdMatrix 2 * geckMatrix 2 = 0 := by
  decide +kernel

theorem simple_commutator_2 : ∀ j : Fin 14,
    simpleMatrix 2 * basisMatrix j - basisMatrix j * simpleMatrix 2 =
      basisCombination (fun k => geckMatrix 2 k j) := by
  decide +kernel

theorem simple_second_conjugation_2 : ∀ j : Fin 14,
    simpleSecondMatrix 2 * basisMatrix j + basisMatrix j * simpleSecondMatrix 2 -
      simpleMatrix 2 * basisMatrix j * simpleMatrix 2 =
        basisCombination (fun k => geckSecondMatrix 2 k j) := by
  decide +kernel

theorem simple_third_conjugation_2 : ∀ j : Fin 14,
    simpleMatrix 2 * basisMatrix j * simpleSecondMatrix 2 -
      simpleSecondMatrix 2 * basisMatrix j * simpleMatrix 2 =
        basisCombination (fun k => geckThirdMatrix 2 k j) := by
  decide +kernel

theorem simple_fourth_conjugation_2 : ∀ j : Fin 14,
    simpleSecondMatrix 2 * basisMatrix j * simpleSecondMatrix 2 = 0 := by
  decide +kernel

end Atlas.Chevalley.Comparison.G2

import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralOperatorData

/-! Literal integral identities. No finite-field or group-order certificate. -/
namespace Atlas.Chevalley.Comparison.G2
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem simple_square_0 :
    simpleMatrix 0 * simpleMatrix 0 = 2 • simpleSecondMatrix 0 := by
  decide +kernel

theorem simple_cube_0 :
    simpleSecondMatrix 0 * simpleMatrix 0 = 0 := by
  decide +kernel

theorem geck_square_0 :
    geckMatrix 0 * geckMatrix 0 = 2 • geckSecondMatrix 0 := by
  decide +kernel

theorem geck_cube_0 :
    geckSecondMatrix 0 * geckMatrix 0 = 3 • geckThirdMatrix 0 := by
  decide +kernel

theorem geck_fourth_0 :
    geckThirdMatrix 0 * geckMatrix 0 = 0 := by
  decide +kernel

theorem simple_commutator_0 : ∀ j : Fin 14,
    simpleMatrix 0 * basisMatrix j - basisMatrix j * simpleMatrix 0 =
      basisCombination (fun k => geckMatrix 0 k j) := by
  decide +kernel

theorem simple_second_conjugation_0 : ∀ j : Fin 14,
    simpleSecondMatrix 0 * basisMatrix j + basisMatrix j * simpleSecondMatrix 0 -
      simpleMatrix 0 * basisMatrix j * simpleMatrix 0 =
        basisCombination (fun k => geckSecondMatrix 0 k j) := by
  decide +kernel

theorem simple_third_conjugation_0 : ∀ j : Fin 14,
    simpleMatrix 0 * basisMatrix j * simpleSecondMatrix 0 -
      simpleSecondMatrix 0 * basisMatrix j * simpleMatrix 0 =
        basisCombination (fun k => geckThirdMatrix 0 k j) := by
  decide +kernel

theorem simple_fourth_conjugation_0 : ∀ j : Fin 14,
    simpleSecondMatrix 0 * basisMatrix j * simpleSecondMatrix 0 = 0 := by
  decide +kernel

end Atlas.Chevalley.Comparison.G2

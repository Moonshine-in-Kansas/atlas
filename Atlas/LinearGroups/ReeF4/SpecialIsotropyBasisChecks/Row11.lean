import Atlas.LinearGroups.ReeF4.SpecialIsotropyBasisChecks.Row10

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem isotropy_coefficients_binary_row11 (j : TraceZeroCoordinate) :
    isotropyCoordinates (extensionCoefficient (F := ZMod 2) (.inr (1,1)) j) =
      isotropyRawStar (isotropyCoordinates (markedBasis (F := ZMod 2) (.inr (1,1))))
        (isotropyCoordinates (markedBasis (F := ZMod 2) j)) := by
  fin_cases j <;> simp only [markedBasis_root,markedBasis_diagonal] <;> decide
end Atlas.ReeF4

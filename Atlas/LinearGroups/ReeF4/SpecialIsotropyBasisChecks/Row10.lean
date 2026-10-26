import Atlas.LinearGroups.ReeF4.SpecialIsotropyBasisChecks.Row09

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem isotropy_coefficients_binary_row10 (j : TraceZeroCoordinate) :
    isotropyCoordinates (extensionCoefficient (F := ZMod 2) (.inr (1,0)) j) =
      isotropyRawStar (isotropyCoordinates (markedBasis (F := ZMod 2) (.inr (1,0))))
        (isotropyCoordinates (markedBasis (F := ZMod 2) j)) := by
  fin_cases j <;> simp only [markedBasis_root,markedBasis_diagonal] <;> decide
end Atlas.ReeF4

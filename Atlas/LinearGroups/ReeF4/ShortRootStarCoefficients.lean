import Atlas.LinearGroups.ReeF4.ShortRootCoordinateComparison
import Atlas.LinearGroups.ReeF4.ShortRootStarCheckBlock2
import Atlas.LinearGroups.ReeF4.ShortRootStarCheckBlock1
import Atlas.LinearGroups.ReeF4.ShortRootStarCheckBlock0
import Atlas.LinearGroups.ReeF4.ShortRootStarCheckDiagonal
import Atlas.LinearGroups.ReeF4.ShortRootStarData

/-! The complete coefficient identity: the equivariance defect factors through
both cross and polar, rather than merely vanishing on a selected list of admissible pairs. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CharP F 2] [CommRing R] [CharP R 2]

theorem shortRootStarCoefficient_map (f : F →+* R) (i j : TraceZeroCoordinate) :
    traceZeroMap f (shortRootStarCoefficient i j) = shortRootStarCoefficient i j := by
  change traceZeroScalarMap f _ = _
  simp only [shortRootStarCoefficient, map_list_sum, List.map_map, Function.comp_def]
  simp only [Function.comp_def, traceZeroScalarMap_apply, extensionCoefficient_map]

set_option maxRecDepth 8192 in
private theorem shortRootStarCoefficient_binary : ∀ i j : TraceZeroCoordinate,
    shortRootStarCoefficient (F := ZMod 2) i j =
      shortRootCoordinateLinear (extensionCoefficient i j) +
        shortRootStarCorrection (traceZeroCross (starMarkedVector i) (starMarkedVector j)) +
        shortRootStarPolarCorrection (traceZeroPolar (starMarkedVector i) (starMarkedVector j)) := by
  rintro (i | ⟨b,k⟩) j
  · exact shortRootStarCheckDiagonal i j
  · fin_cases b
    · exact shortRootStarCheckBlock0 k j
    · exact shortRootStarCheckBlock1 k j
    · exact shortRootStarCheckBlock2 k j

theorem shortRootStarCoefficient_eq (i j : TraceZeroCoordinate) :
    shortRootStarCoefficient (F := F) i j =
      shortRootLinear (extensionCoefficient i j) +
        shortRootStarCorrection (traceZeroCross (starMarkedVector i) (starMarkedVector j)) +
        shortRootStarPolarCorrection (traceZeroPolar (starMarkedVector i) (starMarkedVector j)) := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroScalarMap f) (shortRootStarCoefficient_binary i j)
  simp only [_root_.map_add, traceZeroScalarMap_apply, shortRootStarCoefficient_map,
    shortRootCoordinateLinear_eq, ← shortRootLinear_map, extensionCoefficient_map,
    shortRootStarCorrection_map, shortRootStarPolarCorrection_map,
    ← traceZeroMap_cross, ← traceZeroMap_polar, starMarkedVector_map] at h
  exact h

end Atlas.ReeF4

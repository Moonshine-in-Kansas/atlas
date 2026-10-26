import Atlas.LinearGroups.ReeF4.LongRootStarCheckBlock2
import Atlas.LinearGroups.ReeF4.LongRootStarCheckBlock1
import Atlas.LinearGroups.ReeF4.LongRootStarCheckBlock0
import Atlas.LinearGroups.ReeF4.LongRootStarCheckDiagonal
import Atlas.LinearGroups.ReeF4.LongRootStarData

/-! The complete coefficient identity: the equivariance defect factors through
cross, rather than merely vanishing on a selected list of admissible pairs. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CharP F 2] [CommRing R] [CharP R 2]

theorem longRootStarCoefficient_map (f : F →+* R) (i j : TraceZeroCoordinate) :
    traceZeroMap f (longRootStarCoefficient i j) = longRootStarCoefficient i j := by
  change traceZeroScalarMap f _ = _
  simp only [longRootStarCoefficient, map_list_sum, List.map_map, Function.comp_def]
  simp only [Function.comp_def, traceZeroScalarMap_apply, extensionCoefficient_map]

set_option maxRecDepth 8192 in
private theorem longRootStarCoefficient_binary : ∀ i j : TraceZeroCoordinate,
    longRootStarCoefficient (F := ZMod 2) i j =
      longRootCoordinateLinear (extensionCoefficient i j) +
        longRootStarCorrection (traceZeroCross (starMarkedVector i) (starMarkedVector j)) := by
  rintro (i | ⟨b,k⟩) j
  · exact longRootStarCheckDiagonal i j
  · fin_cases b
    · exact longRootStarCheckBlock0 k j
    · exact longRootStarCheckBlock1 k j
    · exact longRootStarCheckBlock2 k j

theorem longRootStarCoefficient_eq (i j : TraceZeroCoordinate) :
    longRootStarCoefficient (F := F) i j =
      longRootLinear (extensionCoefficient i j) +
        longRootStarCorrection (traceZeroCross (starMarkedVector i) (starMarkedVector j)) := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroScalarMap f) (longRootStarCoefficient_binary i j)
  simp only [_root_.map_add, traceZeroScalarMap_apply, longRootStarCoefficient_map,
    longRootCoordinateLinear_eq, ← longRootLinear_map, extensionCoefficient_map,
    longRootStarCorrection_map, ← traceZeroMap_cross, starMarkedVector_map] at h
  exact h

end Atlas.ReeF4

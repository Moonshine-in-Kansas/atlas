import Atlas.LinearGroups.ReeF4.SpecialIsotropyBasisChecks.Row25

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R] [CharP F 2] [CharP R 2]

private theorem coefficients_binary (i j : TraceZeroCoordinate) :
    isotropyCoordinates (extensionCoefficient (F := ZMod 2) i j) =
      isotropyRawStar (isotropyCoordinates (markedBasis (F := ZMod 2) i))
        (isotropyCoordinates (markedBasis (F := ZMod 2) j)) := by
  fin_cases i
  · exact isotropy_coefficients_binary_row0 j
  · exact isotropy_coefficients_binary_row1 j
  · exact isotropy_coefficients_binary_row2 j
  · exact isotropy_coefficients_binary_row3 j
  · exact isotropy_coefficients_binary_row4 j
  · exact isotropy_coefficients_binary_row5 j
  · exact isotropy_coefficients_binary_row6 j
  · exact isotropy_coefficients_binary_row7 j
  · exact isotropy_coefficients_binary_row8 j
  · exact isotropy_coefficients_binary_row9 j
  · exact isotropy_coefficients_binary_row10 j
  · exact isotropy_coefficients_binary_row11 j
  · exact isotropy_coefficients_binary_row12 j
  · exact isotropy_coefficients_binary_row13 j
  · exact isotropy_coefficients_binary_row14 j
  · exact isotropy_coefficients_binary_row15 j
  · exact isotropy_coefficients_binary_row16 j
  · exact isotropy_coefficients_binary_row17 j
  · exact isotropy_coefficients_binary_row18 j
  · exact isotropy_coefficients_binary_row19 j
  · exact isotropy_coefficients_binary_row20 j
  · exact isotropy_coefficients_binary_row21 j
  · exact isotropy_coefficients_binary_row22 j
  · exact isotropy_coefficients_binary_row23 j
  · exact isotropy_coefficients_binary_row24 j
  · exact isotropy_coefficients_binary_row25 j

private theorem coefficients (i j : TraceZeroCoordinate) :
    isotropyCoordinates (extensionCoefficient (F := F) i j) =
      isotropyRawStar (isotropyCoordinates (markedBasis (F := F) i))
        (isotropyCoordinates (markedBasis (F := F) j)) := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (fun z : Fin 26 → ZMod 2 => fun k => f (z k))
    (coefficients_binary i j)
  rw [← isotropyCoordinates_map,extensionCoefficient_map,← isotropyRawStar_map] at h
  have hi := isotropyCoordinates_map f (markedBasis (F := ZMod 2) i)
  have hj := isotropyCoordinates_map f (markedBasis (F := ZMod 2) j)
  rw [isotropyMarkedBasis_map] at hi hj
  simpa only [← hi,← hj] using h

theorem isotropyRawStar_actual_bilinear (u v : TraceZero F) :
    isotropyCoordinates (proposedStarLinear (wedge u v)) =
      isotropyRawStar (isotropyCoordinates u) (isotropyCoordinates v) := by
  have h : isotropyActualBilinear (F := F) = isotropyRawOnTraceZero := by
    apply markedBasis.ext
    intro i
    apply markedBasis.ext
    intro j
    change isotropyCoordinates (proposedStarLinear (wedge (markedBasis i) (markedBasis j))) = _
    rw [proposedStarLinear_marked_wedge]
    exact coefficients i j
  exact congrArg (fun b : TraceZero F →ₗ[F] TraceZero F →ₗ[F] (Fin 26 → F) => b u v) h
end Atlas.ReeF4

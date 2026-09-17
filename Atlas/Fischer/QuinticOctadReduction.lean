import Atlas.Fischer.QuinticOctadARows
import Atlas.Fischer.QuinticOctadBRows
import Atlas.Fischer.QuinticOctadC0Rows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- All distinct-sextet contractions except the pure-octad network are evaluated. -/
theorem coordinateQuintic_sextet_reduced (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    coordinateQuintic (.inr D) (.inr E) (.inr F) =
      (1199 / 8 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) +
        quinticOctadBlockWWW_WWW D E F := by
  rw [coordinateQuintic_octad_four_blocks, quinticOctad_A_sextet D E F hF,
    quinticOctad_B_sextet D E F hF, quinticOctad_C0_sextet D E F hF]
  ring

/-- All distinct-trio contractions except the pure-octad network are evaluated. -/
theorem coordinateQuintic_trio_reduced (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    coordinateQuintic (.inr D) (.inr E) (.inr F) =
      (1147 / 8 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) +
        quinticOctadBlockWWW_WWW D E F := by
  rw [coordinateQuintic_octad_four_blocks, quinticOctad_A_trio D E F hF,
    quinticOctad_B_trio D E F hF, quinticOctad_C0_trio D E F hF]
  ring

/-- Conditional final sextet closure: the remaining pure-octad value stays explicit. -/
theorem coordinateQuintic_sextet_of_pure_octad (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E)
    (hD0 : quinticOctadBlockWWW_WWW D E F =
      (13634 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F)) :
    coordinateQuintic (.inr D) (.inr E) (.inr F) =
      1002 * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  rw [coordinateQuintic_sextet_reduced D E F hF, hD0]
  ring

/-- Conditional final trio closure, with the actual theta-phase coefficient. -/
theorem coordinateQuintic_trio_of_pure_octad (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne)
    (hD0 : quinticOctadBlockWWW_WWW D E F =
      (13738 / 16 : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F)) :
    coordinateQuintic (.inr D) (.inr E) (.inr F) =
      1002 * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  rw [coordinateQuintic_trio_reduced D E F hF, hD0]
  ring

end Atlas.Fischer

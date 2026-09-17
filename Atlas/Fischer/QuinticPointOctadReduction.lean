import Atlas.Fischer.QuinticPointOctadUUU
import Atlas.Fischer.QuinticPointOctadGram
import Atlas.Fischer.QuinticPointOctadNeighbors
import Atlas.Fischer.QuinticPointOctadSymmetry
import Atlas.Fischer.QuinticPointOctadMixed

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Exact source UWW contribution, including its transpose and equal-slot multiplicities. -/
theorem quinticPointOctad_UWW_ratio (p : Omega) (D : Octad) :
    quinticPointOctadUWW_UUU p D + quinticPointOctadUWW_UWW p D +
      quinticPointOctadWUW_WWU p D + quinticPointOctadWUW_WWW p D +
      quinticPointOctadWWU_WUW p D + quinticPointOctadWWU_WWW p D =
    (if p ∈ D.val then (3077 / 16 : Scalar) else 1377 / 16) *
      coordinateCubic (.inl p) (.inr D) (.inr D) := by
  rw [quinticPointOctadUWW_UUU_eq, quinticPointOctadWWU_WUW_eq,
    quinticPointOctadWWU_WWW_eq, quinticPointOctadUUU_UWW_ratio,
    quinticPointOctadUWW_UWW_eq, quinticPointOctadWUW_WWU_ratio,
    quinticPointOctadWUW_WWW_ratio, coordinateCubic_point_octads]
  by_cases hp : p ∈ D.val <;> norm_num [cubicPointOctadIncidence, hp]

/-- All repeated-octad contributions except the purely octadic network are evaluated. -/
theorem coordinateQuintic_point_octad_reduced (p : Omega) (D : Octad) :
    coordinateQuintic (.inl p) (.inr D) (.inr D) =
      (if p ∈ D.val then (2001 / 8 : Scalar) else 1161 / 8) *
        coordinateCubic (.inl p) (.inr D) (.inr D) + quinticPointOctadWWW_WWW p D := by
  rw [coordinateQuintic_point_octad_five_blocks, quinticPointOctadUUU_UWW_ratio,
    quinticPointOctadUWW_UWW_eq, quinticPointOctadWUW_WWU_ratio,
    quinticPointOctadWUW_WWW_ratio, coordinateCubic_point_octads]
  by_cases hp : p ∈ D.val <;> norm_num [cubicPointOctadIncidence, hp]

end Atlas.Fischer

import Atlas.Fischer.CountingCanonicalSignedSum
import Atlas.Fischer.QuinticOctadReduction
import Atlas.Fischer.QuinticUniversalReduction

noncomputable section
namespace Atlas.Fischer

/-- The canonical sextet coefficient, with its actual signed pure-octad sum. -/
theorem coordinateQuintic_canonical_sextet :
    coordinateQuintic (.inr countingCanonicalD) (.inr countingCanonicalSextetE)
      (.inr countingCanonicalSextetF) =
    1002 * coordinateCubic (.inr countingCanonicalD) (.inr countingCanonicalSextetE)
      (.inr countingCanonicalSextetF) := by
  apply coordinateQuintic_sextet_of_pure_octad _ _ _ countingCanonicalSextet_word
  rw [quinticOctadBlockWWW_WWW_eq_signed_sum _ _ _ countingCanonicalSextet_triangle_line,
    countingCanonicalSextet_signed_sum]
  push_cast
  ring

/-- The canonical trio coefficient, retaining the actual theta phase. -/
theorem coordinateQuintic_canonical_trio :
    coordinateQuintic (.inr countingCanonicalD) (.inr countingCanonicalTrioE)
      (.inr countingCanonicalTrioF) =
    1002 * coordinateCubic (.inr countingCanonicalD) (.inr countingCanonicalTrioE)
      (.inr countingCanonicalTrioF) := by
  apply coordinateQuintic_trio_of_pure_octad _ _ _ countingCanonicalTrio_word
  rw [quinticOctadBlockWWW_WWW_eq_signed_sum _ _ _ countingCanonicalTrio_triangle_line,
    countingCanonicalTrio_signed_sum]
  push_cast
  ring

/-- The exact universal weighted quintic tensor identity for the retained
783-dimensional Golay/Parker algebra. All seven support families and all
vanishing coefficients are included, with no numerical tensor hypothesis. -/
theorem coordinateQuintic_eq_1002_coordinateCubic (p q r : CoordinateIndex) :
    coordinateQuintic p q r = 1002 * coordinateCubic p q r :=
  coordinateQuintic_universal_of_canonical coordinateQuintic_canonical_sextet
    coordinateQuintic_canonical_trio p q r

end Atlas.Fischer

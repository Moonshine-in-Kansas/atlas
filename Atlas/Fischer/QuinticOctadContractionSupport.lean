import Atlas.Fischer.OctadContractionPairWeight
import Atlas.Fischer.QuinticOctadBlocks
import Atlas.Fischer.CubicOctadDiamondSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The same five actual cubic coefficients, with the three external edges oriented first. -/
def octadContractionCoefficient (D E F G H J GP HP JP : Octad) : Scalar :=
  star (coordinateCubic (.inr G) (.inr H) (.inr J)) *
    star (coordinateCubic (.inr GP) (.inr HP) (.inr JP)) *
    coordinateCubic (.inr D) (.inr G) (.inr GP) *
    coordinateCubic (.inr E) (.inr H) (.inr HP) *
    coordinateCubic (.inr F) (.inr J) (.inr JP)

theorem coordinateCubic_swap_outer (a b c : CoordinateIndex) :
    coordinateCubic a b c = coordinateCubic c b a := by
  rw [coordinateCubic_swap_first a b c, coordinateCubic_swap_last b a c,
    coordinateCubic_swap_first b c a]

theorem coordinateQuinticCubicProduct_octad_coefficient (D E F G H J GP HP JP : Octad) :
    coordinateQuinticCubicProduct (.inr G) (.inr H) (.inr J)
      (.inr GP) (.inr HP) (.inr JP) (.inr D) (.inr E) (.inr F) =
      octadContractionCoefficient D E F G H J GP HP JP := by
  unfold coordinateQuinticCubicProduct octadContractionCoefficient
  rw [coordinateCubic_swap_outer (.inr GP) (.inr G) (.inr D),
    coordinateCubic_swap_outer (.inr HP) (.inr H) (.inr E),
    coordinateCubic_swap_outer (.inr JP) (.inr J) (.inr F)]

theorem coordinateCubic_octad_off_diamond (D E X : Octad) (h : OctadPairAdmissible D E)
    (hx : X ≠ octadDiamond D E h) : coordinateCubic (.inr D) (.inr E) (.inr X) = 0 := by
  classical
  rw [coordinateCubic_octad_delta D E X h, if_neg hx]

/-- All four completion indices are forced by actual cubic support. -/
theorem octadContractionCoefficient_sum (D E F G H : Octad)
    (hGH : OctadPairAdmissible G H) (hDG : OctadPairAdmissible D G)
    (hEH : OctadPairAdmissible E H)
    (hFJ : OctadPairAdmissible F (octadDiamond G H hGH)) :
    (∑ J : Octad, ∑ GP : Octad, ∑ HP : Octad, ∑ JP : Octad,
      octadContractionCoefficient D E F G H J GP HP JP) =
      octadContractionCoefficient D E F G H (octadDiamond G H hGH)
        (octadDiamond D G hDG) (octadDiamond E H hEH)
        (octadDiamond F (octadDiamond G H hGH) hFJ) := by
  classical
  calc
    _ = ∑ GP : Octad, ∑ HP : Octad, ∑ JP : Octad,
        octadContractionCoefficient D E F G H (octadDiamond G H hGH) GP HP JP := by
      apply Finset.sum_eq_single (octadDiamond G H hGH)
      · intro J hJ hn
        have hz := coordinateCubic_octad_off_diamond G H J hGH hn
        simp only [octadContractionCoefficient, hz, star_zero, zero_mul, Finset.sum_const_zero]
      · simp
    _ = ∑ HP : Octad, ∑ JP : Octad,
        octadContractionCoefficient D E F G H (octadDiamond G H hGH)
          (octadDiamond D G hDG) HP JP := by
      apply Finset.sum_eq_single (octadDiamond D G hDG)
      · intro GP hGP hn
        have hz := coordinateCubic_octad_off_diamond D G GP hDG hn
        simp only [octadContractionCoefficient, hz, mul_zero, zero_mul, Finset.sum_const_zero]
      · simp
    _ = ∑ JP : Octad,
        octadContractionCoefficient D E F G H (octadDiamond G H hGH)
          (octadDiamond D G hDG) (octadDiamond E H hEH) JP := by
      apply Finset.sum_eq_single (octadDiamond E H hEH)
      · intro HP hHP hn
        have hz := coordinateCubic_octad_off_diamond E H HP hEH hn
        simp only [octadContractionCoefficient, hz, mul_zero, zero_mul, Finset.sum_const_zero]
      · simp
    _ = _ := by
      apply Finset.sum_eq_single (octadDiamond F (octadDiamond G H hGH) hFJ)
      · intro JP hJP hn
        have hz := coordinateCubic_octad_off_diamond F (octadDiamond G H hGH) JP hFJ hn
        simp only [octadContractionCoefficient, hz, mul_zero]
      · simp

end Atlas.Fischer

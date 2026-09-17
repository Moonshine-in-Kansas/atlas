import Atlas.Fischer.CalibratedOctadCubic
import Atlas.Fischer.OctadQuadrilateralClosure
import Atlas.Fischer.OctadQuadrilateralSigns
import Atlas.Fischer.CubicOctadQuadrilateralEdges

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem omegaOctadCubic_of_line (i : Omega) (D E F : Octad)
    (h : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    omegaOctadCubic i D E F = star (theta ^ octadDelta D E / 2 *
      parkerScalarSign (parkerOmegaFactorSet i (octadWord D) (octadWord E))) := by
  have ha := octadPairAdmissible_of_line D E F h
  rw [octadDiamond_eq_of_line D E F ha h]
  exact omegaOctadCubic_diamond i D E ha

/-- Each sign change of a coordinate occurs twice around the quadrilateral,
so this contraction is unchanged by the explicit calibration. -/
theorem cubicOctadQuadrilateralWeight_calibrated (i : Omega) (D F G : Octad)
    (hDF : OctadPairAdmissible D F) (hDG : OctadPairAdmissible D G)
    (hFG : OctadPairAdmissible F G) :
    cubicOctadQuadrilateralWeight D F G hDF hDG hFG =
      star (omegaOctadCubic i F G (octadDiamond F G hFG)) *
      star (omegaOctadCubic i (octadDiamond D F hDF) (octadDiamond D G hDG)
        (octadDiamond F G hFG)) *
      omegaOctadCubic i D F (octadDiamond D F hDF) *
      omegaOctadCubic i D G (octadDiamond D G hDG) := by
  unfold cubicOctadQuadrilateralWeight omegaOctadCubic
  simp only [star_mul, parkerScalarSign_star]
  have hs (a b c d e f : ParkerBit) :
      parkerScalarSign (b + c + d) * parkerScalarSign (e + f + d) *
        parkerScalarSign (a + b + e) * parkerScalarSign (a + c + f) = 1 := by
    rw [← parkerScalarSign_add, ← parkerScalarSign_add, ← parkerScalarSign_add]
    have hz : b + c + d + (e + f + d) + (a + b + e) + (a + c + f) = 0 := by
      ring_nf
      simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]
    rw [hz]
    rfl
  have hcycle (A B C : Octad) : coordinateCubic (.inr A) (.inr B) (.inr C) =
      coordinateCubic (.inr B) (.inr C) (.inr A) := by
    rw [coordinateCubic_swap_first, coordinateCubic_swap_last]
  rw [hcycle (octadDiamond F G hFG) F G,
    hcycle (octadDiamond F G hFG) (octadDiamond D F hDF) (octadDiamond D G hDG),
    coordinateCubic_swap_last (.inr D) (.inr (octadDiamond D F hDF)) (.inr F),
    coordinateCubic_swap_last (.inr D) (.inr (octadDiamond D G hDG)) (.inr G)]
  linear_combination -(hs (parkerOmegaGauge i (octadWord D))
    (parkerOmegaGauge i (octadWord F)) (parkerOmegaGauge i (octadWord G))
    (parkerOmegaGauge i (octadWord (octadDiamond F G hFG)))
    (parkerOmegaGauge i (octadWord (octadDiamond D F hDF)))
    (parkerOmegaGauge i (octadWord (octadDiamond D G hDG)))) *
      star (coordinateCubic (.inr F) (.inr G) (.inr (octadDiamond F G hFG))) *
      star (coordinateCubic (.inr (octadDiamond D F hDF))
        (.inr (octadDiamond D G hDG)) (.inr (octadDiamond F G hFG))) *
      coordinateCubic (.inr D) (.inr F) (.inr (octadDiamond D F hDF)) *
      coordinateCubic (.inr D) (.inr G) (.inr (octadDiamond D G hDG))

end Atlas.Fischer

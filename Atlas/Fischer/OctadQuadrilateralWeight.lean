import Atlas.Fischer.CalibratedQuadrilateral

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Exact signed scalar weight of every actual admissible quadrilateral.
The conjugations and all four triangle types are retained explicitly. -/
theorem cubicOctadQuadrilateralWeight_formula (D F G : Octad)
    (hDF : OctadPairAdmissible D F) (hDG : OctadPairAdmissible D G)
    (hFG : OctadPairAdmissible F G) :
    16 * cubicOctadQuadrilateralWeight D F G hDF hDG hFG =
      parkerScalarSign ((D.val ∩ F.val ∩ G.val).card : ParkerBit) *
        theta ^ octadDelta F G *
        theta ^ octadDelta (octadDiamond D F hDF) (octadDiamond D G hDG) *
        star (theta ^ octadDelta D F) * star (theta ^ octadDelta D G) := by
  let i : Omega := Classical.choice inferInstance
  rw [cubicOctadQuadrilateralWeight_calibrated i,
    omegaOctadCubic_diamond, omegaOctadCubic_of_line i _ _ _
      (octad_quadrilateral_triangle_closure D F G hDF hDG hFG),
    omegaOctadCubic_diamond, omegaOctadCubic_diamond]
  simp only [star_star, star_mul, star_div₀, star_ofNat, parkerScalarSign_star]
  have hs := congrArg parkerScalarSign
    (parkerOmegaFactorSet_octad_quadrilateral i D F G hDF hDG)
  simp only [parkerScalarSign_add] at hs
  linear_combination hs * theta ^ octadDelta F G *
    theta ^ octadDelta (octadDiamond D F hDF) (octadDiamond D G hDG) *
    star (theta ^ octadDelta D F) * star (theta ^ octadDelta D G)

end Atlas.Fischer

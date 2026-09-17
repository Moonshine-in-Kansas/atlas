import Atlas.Fischer.CalibratedQuadrilateral
import Atlas.Fischer.CalibratedQuintic
import Atlas.Fischer.OctadContractionSigns
import Atlas.Fischer.OctadDiamondParity
import Atlas.Fischer.QuinticSignedScalar

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def octadContractionIntegerWeight (D E F G H J GP HP : Octad) : ℤ :=
  let s := (E.val ∩ G.val).card / 2 + (D.val ∩ E.val ∩ H.val).card +
    (D.val ∩ G.val ∩ H.val).card
  (-1 : ℤ)^(s + octadDelta G H + octadDelta GP HP) *
    (-3 : ℤ)^((octadDelta G H + octadDelta D G + octadDelta E H +
      octadDelta F J + octadDelta GP HP - octadDelta D E)/2)

/-- The literal signed integer summand is derived from the actual five cubic
coefficients. The sixth triangle follows from retained Golay closure. -/
theorem coordinateQuinticCubicProduct_octad_weight (D E F G H J GP HP JP : Octad)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine)
    (hGH : octadWord G + octadWord H + octadWord J ∈ allOneCodeLine)
    (hDG : octadWord D + octadWord G + octadWord GP ∈ allOneCodeLine)
    (hEH : octadWord E + octadWord H + octadWord HP ∈ allOneCodeLine)
    (hFJ : octadWord F + octadWord J + octadWord JP ∈ allOneCodeLine) :
    16 * coordinateQuinticCubicProduct (.inr G) (.inr H) (.inr J)
      (.inr GP) (.inr HP) (.inr JP) (.inr D) (.inr E) (.inr F) =
      coordinateCubic (.inr D) (.inr E) (.inr F) *
        (octadContractionIntegerWeight D E F G H J GP HP : Scalar) := by
  let i : Omega := Classical.choice inferInstance
  have aDE := octadPairAdmissible_of_line D E F hDE
  have aGH := octadPairAdmissible_of_line G H J hGH
  have aDG := octadPairAdmissible_of_line D G GP hDG
  have aEH := octadPairAdmissible_of_line E H HP hEH
  have eF := octadDiamond_eq_of_line D E F aDE hDE
  have eJ := octadDiamond_eq_of_line G H J aGH hGH
  have eGP := octadDiamond_eq_of_line D G GP aDG hDG
  have eHP := octadDiamond_eq_of_line E H HP aEH hEH
  have hlast := octad_contraction_triangle_closure D E F G H J GP HP JP hDE hGH hDG hEH hFJ
  have hs := parkerOmegaFactorSet_octad_contraction i D E G H aDE aGH aDG aEH
  rw [← eF, ← eJ, ← eGP, ← eHP] at hs
  have hb := octad_contraction_delta_parity D E F G H J GP HP JP hDE hGH hDG hEH hFJ
  have hp := congrArg (fun z : Bit => z.val) hb
  simp only [ZMod.val_natCast] at hp
  rw [Nat.mod_eq_of_lt (show octadDelta D E < 2 from by
    have h := octadDelta_le_one D E; omega)] at hp
  have hc := quintic_signed_scalar (octadDelta D E) (octadDelta G H)
    (octadDelta D G) (octadDelta E H) (octadDelta F J) (octadDelta GP HP)
    ((E.val ∩ G.val).card / 2 + (D.val ∩ E.val ∩ H.val).card +
      (D.val ∩ G.val ∩ H.val).card)
    (parkerOmegaFactorSet i (octadWord D) (octadWord E))
    (parkerOmegaFactorSet i (octadWord G) (octadWord H))
    (parkerOmegaFactorSet i (octadWord D) (octadWord G))
    (parkerOmegaFactorSet i (octadWord E) (octadWord H))
    (parkerOmegaFactorSet i (octadWord F) (octadWord J))
    (parkerOmegaFactorSet i (octadWord GP) (octadWord HP))
    (octadDelta_le_one D E) (octadDelta_le_one G H) (octadDelta_le_one D G)
    (octadDelta_le_one E H) (octadDelta_le_one F J) (octadDelta_le_one GP HP) hp hs
  have hw : (octadContractionIntegerWeight D E F G H J GP HP : Scalar) =
      (-1 : Scalar)^((E.val ∩ G.val).card / 2 + (D.val ∩ E.val ∩ H.val).card +
        (D.val ∩ G.val ∩ H.val).card + octadDelta G H + octadDelta GP HP) *
      (-3 : Scalar)^((octadDelta G H + octadDelta D G + octadDelta E H +
        octadDelta F J + octadDelta GP HP - octadDelta D E)/2) := by
    simp only [octadContractionIntegerWeight, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  have hcal : 16 * omegaOctadQuintic i G H J GP HP JP D E F =
      omegaOctadCubic i D E F * (octadContractionIntegerWeight D E F G H J GP HP : Scalar) := by
    unfold omegaOctadQuintic
    rw [omegaOctadCubic_cycle i GP G D, omegaOctadCubic_cycle i HP H E,
      omegaOctadCubic_cycle i JP J F]
    rw [omegaOctadCubic_of_line i G H J hGH, omegaOctadCubic_of_line i GP HP JP hlast,
      omegaOctadCubic_of_line i D G GP hDG, omegaOctadCubic_of_line i E H HP hEH,
      omegaOctadCubic_of_line i F J JP hFJ, omegaOctadCubic_of_line i D E F hDE, hw]
    simpa only [star_star, mul_assoc] using hc
  rw [omegaOctadQuintic_calibration, omegaOctadCubic] at hcal
  have hn : parkerScalarSign (parkerOmegaGauge i (octadWord D) +
      parkerOmegaGauge i (octadWord E) + parkerOmegaGauge i (octadWord F)) ≠ 0 := by
    intro hz
    have ht := parkerScalarSign_square (parkerOmegaGauge i (octadWord D) +
      parkerOmegaGauge i (octadWord E) + parkerOmegaGauge i (octadWord F))
    rw [hz, zero_mul] at ht
    exact zero_ne_one ht
  apply mul_left_cancel₀ hn
  linear_combination hcal

end Atlas.Fischer

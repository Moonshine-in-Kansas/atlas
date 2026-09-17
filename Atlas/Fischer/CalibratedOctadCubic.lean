import Atlas.Fischer.ParkerOmegaGauge
import Atlas.Fischer.OctadDiamond
import Atlas.Fischer.CubicSliceOctadRows
import Atlas.Fischer.SignedMonomialGeometry

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def omegaOctadCubic (i : Omega) (D E F : Octad) : Scalar :=
  parkerScalarSign (parkerOmegaGauge i (octadWord D) +
    parkerOmegaGauge i (octadWord E) + parkerOmegaGauge i (octadWord F)) *
      coordinateCubic (.inr D) (.inr E) (.inr F)

/-- The changed coefficients evaluate the actual cubic on a signed basis. -/
theorem omegaOctadCubic_evaluation (i : Omega) (D E F : Octad) :
    omegaOctadCubic i D E F =
      cubic (parkerScalarSign (parkerOmegaGauge i (octadWord D)) • coordinateVector (.inr D))
        (parkerScalarSign (parkerOmegaGauge i (octadWord E)) • coordinateVector (.inr E))
        (parkerScalarSign (parkerOmegaGauge i (octadWord F)) • coordinateVector (.inr F)) := by
  simp only [omegaOctadCubic, cubic_smul_first, cubic_smul_second, cubic_smul_third,
    parkerScalarSign_add, coordinateCubic, mul_assoc]
  ring

theorem omegaOctadCubic_diamond (i : Omega) (D E : Octad) (h : OctadPairAdmissible D E) :
    omegaOctadCubic i D E (octadDiamond D E h) =
      star (theta ^ octadDelta D E / 2 *
        parkerScalarSign (parkerOmegaFactorSet i (octadWord D) (octadWord E))) := by
  classical
  have hw := octadDiamond_word D E h
  unfold omegaOctadCubic
  rw [coordinateCubic_octad_product, octadBasisProduct_octad_apply]
  by_cases h4 : (D.val ∩ E.val).card = 4
  · have h0 : (D.val ∩ E.val).card ≠ 0 := by omega
    simp only [h0, ite_false, add_zero] at hw
    have hf : parkerOmegaFactorSet i (octadWord D) (octadWord E) =
        parkerGolayFactorSet (octadWord D) (octadWord E) +
          parkerOmegaGauge i (octadWord D) + parkerOmegaGauge i (octadWord E) +
            parkerOmegaGauge i (octadWord (octadDiamond D E h)) := by
      rw [hw]
      rfl
    rw [if_pos hw, hf]
    simp only [octadDelta, h0, ite_false, pow_zero, parkerScalarSign_add,
      star_mul, parkerScalarSign_star, star_div₀, star_one, star_ofNat]
    ring
  · have h0 := h.resolve_left h4
    simp only [h0, ite_true] at hw
    have hn : octadWord (octadDiamond D E h) ≠ octadWord D + octadWord E := by
      intro hh
      have hh4 := octadWord_sum_weight (octadDiamond D E h) D E hh
      exact h4 (by simpa only [signedOctadIntersection, signedOctadSupport_canonical] using hh4)
    have hf : parkerOmegaFactorSet i (octadWord D) (octadWord E) =
        (parkerGolayFactorSet (octadWord D) (octadWord E) +
          parkerGolayFactorSet (octadWord D + octadWord E) golayOne) +
          parkerOmegaGauge i (octadWord D) + parkerOmegaGauge i (octadWord E) +
            parkerOmegaGauge i (octadWord (octadDiamond D E h)) := by
      rw [hw, parkerOmegaGauge_add_one]
      unfold parkerOmegaFactorSet parkerChangedFactorSet
      ring_nf
      simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]
    rw [if_neg hn, if_pos hw, hf]
    simp only [octadDelta, h0, ite_true, pow_one, parkerScalarSign_add,
      star_mul, parkerScalarSign_star, star_div₀, star_one, star_ofNat]
    ring

end Atlas.Fischer

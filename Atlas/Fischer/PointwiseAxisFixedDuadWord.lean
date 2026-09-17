import Atlas.Fischer.PointwiseAxisSignCharacter
import Atlas.Fischer.DuadWordCoefficient

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Fixing a complete duadic coordinate expression fixes its real octad
coefficients and conjugates its imaginary coefficients according to parity. -/
theorem pointwiseAxis_fixed_duad_word_sign (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (p : Finset Omega) (hp : p.Nonempty)
    (η : DuadCoordinateWord p → Bit) (ξ : Module.Dual Bit (duadShortenedCode p))
    (hfix : e.val (duadSignedCoordinateExpression p η ξ)=duadSignedCoordinateExpression p η ξ)
    (c : DuadCoordinateWord p) :
    pointwiseAxisOctadSign e (duadWordOctad p c)=
      if hammingNorm c.val.val.val=8 then 0 else semilinearAlgebraParity e := by
  classical
  have h := pointwiseAxis_octad_coordinate_relation e he (duadWordOctad p c)
    (duadSignedCoordinateExpression p η ξ)
  rw [hfix,← pointwiseAxisOctadSign_scalar e he] at h
  have hn := duadSignedCoordinateExpression_at_word_ne_zero p hp η ξ c
  have hs := duadSignedCoordinateExpression_at_word_star p hp η ξ c
  apply parkerScalarSign_injective
  rcases (show ∀ b : Bit, b=0 ∨ b=1 from by decide) (semilinearAlgebraParity e) with hb | hb
  · rw [hb,scalarParityAut_zero] at h
    have heq := mul_right_cancel₀ hn (h.trans (one_mul _).symm)
    simpa [hb,parkerScalarSign] using heq
  · rw [hb,scalarParityAut_one,hs] at h
    by_cases h8 : hammingNorm c.val.val.val=8
    · rw [if_pos h8] at h
      have heq := mul_right_cancel₀ hn (h.trans (one_mul _).symm)
      simpa [h8,parkerScalarSign] using heq
    · rw [if_neg h8] at h
      have heq := mul_right_cancel₀ hn (h.trans (neg_one_mul _).symm)
      simpa [h8,hb,parkerScalarSign] using heq

end Atlas.Fischer

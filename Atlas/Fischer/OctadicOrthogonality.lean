import Atlas.Fischer.OctadicRootCoordinates
import Atlas.Fischer.CoordinateHermitianSums

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem calibratedHyperplaneSupport_injective {O : Octad} (Q : OctadCalibration O) :
    Function.Injective (fun b => signedOctadSupport (calibratedHyperplaneLift Q b)) := by
  intro b c h
  have he := congrArg octadWord h
  simp only [octadWord_signedSupport] at he
  exact Subtype.ext (Subtype.ext he)

theorem calibratedHyperplaneVector_orthonormal {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) :
    hermitian (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q c) =
      if b = c then 1 else 0 := by
  classical
  by_cases h : b = c
  · subst c
    rw [calibratedHyperplaneVector_norm, ite_eq_left rfl]
  · have hs := fun he => h (calibratedHyperplaneSupport_injective Q he)
    simp only [calibratedHyperplaneVector, signedOctadVector, hermitian_smul_left,
      hermitian_smul_right, hermitian_xOctad, ite_eq_right hs, ite_eq_right h, mul_zero]

theorem octadWord_not_shortened (O : Octad) : octadWord O ∉ octadShortenedCode O := by
  intro h
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < O.val.card by rw [octad_size O.val O.property]; decide)
  have hz := (mem_octadShortenedCode O (octadWord O)).mp h i hi
  simp only [octadWord_apply, ite_eq_left hi] at hz
  exact one_ne_zero hz

theorem calibratedHyperplaneSupport_ne_octad {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    signedOctadSupport (calibratedHyperplaneLift Q b) ≠ O := by
  intro h
  have he := congrArg octadWord h
  rw [octadWord_signedSupport] at he
  exact octadWord_not_shortened O (he ▸ b.val.property)

theorem hermitian_octad_calibratedHyperplane {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (signedOctadVector Q.octadLift) (calibratedHyperplaneVector Q b) = 0 := by
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  have hn := Ne.symm (calibratedHyperplaneSupport_ne_octad Q b)
  simp only [calibratedHyperplaneVector, signedOctadVector, hermitian_smul_left,
    hermitian_smul_right, hermitian_xOctad, ho, ite_eq_right hn, mul_zero]

theorem octadicAxisPart_axis_apply (O : Octad) (i : Omega) :
    octadicAxisPart O (.inl i) = if i ∈ O.val then -1 else 1 := by
  classical
  by_cases hi : i ∈ O.val <;>
    simp [octadicAxisPart, Finset.sum_apply, hi]

@[simp] theorem octadicAxisPart_octad_apply (O P : Octad) :
    octadicAxisPart O (.inr P) = 0 := by
  simp [octadicAxisPart, Finset.sum_apply]

theorem octadicAxisPart_norm (O : Octad) : hermitian (octadicAxisPart O) (octadicAxisPart O) = 3 := by
  classical
  unfold hermitian weightedHermitian
  rw [Fintype.sum_sum_type]
  have hh (i : Omega) : (coordinateWeight (.inl i) : Scalar) * octadicAxisPart O (.inl i) *
      star (octadicAxisPart O (.inl i)) = 1 / 8 := by
    rw [octadicAxisPart_axis_apply]
    split_ifs <;> norm_num [coordinateWeight]
  simp only [hh, octadicAxisPart_octad_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card Omega = 24 := by decide
  rw [hc]
  norm_num

theorem hermitian_octadicAxis_signedOctad (O : Octad) (d : SignedOctad) :
    hermitian (octadicAxisPart O) (signedOctadVector d) = 0 := by
  simp only [octadicAxisPart, neg_add_eq_sub, hermitian_sub_left,
    hermitian_sum_left, signedOctadVector, hermitian_smul_right, hermitian_u_xOctad,
    mul_zero, Finset.sum_const_zero, sub_self]

end Atlas.Fischer

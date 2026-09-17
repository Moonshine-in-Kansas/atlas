import Atlas.Fischer.OctadicRootEquations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem parkerScalarSign_ne_zero (b : Bit) : parkerScalarSign b ≠ 0 := by
  intro h
  have hs := parkerScalarSign_square b
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

theorem parkerScalarSign_injective : Function.Injective parkerScalarSign := by
  intro a b h
  have hz : a + b = 0 := (parkerScalarSign_eq_one_iff _).mp (by
    rw [parkerScalarSign_add, h, parkerScalarSign_square])
  exact (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq b)

theorem theta_ne_zero : theta ≠ 0 := by
  intro h
  have hs := theta_sq
  rw [h] at hs
  norm_num at hs

theorem calibratedHyperplaneVector_at_octad {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) : calibratedHyperplaneVector Q b (.inr O) = 0 := by
  simp only [calibratedHyperplaneVector, signedOctadVector, Pi.smul_apply, smul_eq_mul,
    xOctad_octad_apply, ite_eq_right (Ne.symm (calibratedHyperplaneSupport_ne_octad Q b)),
    mul_zero]

theorem calibratedHyperplaneVector_at_support {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) :
    calibratedHyperplaneVector Q b (.inr (signedOctadSupport (calibratedHyperplaneLift Q c))) =
      if c = b then parkerScalarSign (Q.parkerSection.sign b.val) else 0 := by
  have hh : signedOctadSupport (calibratedHyperplaneLift Q c) =
      signedOctadSupport (calibratedHyperplaneLift Q b) ↔ c = b :=
    (calibratedHyperplaneSupport_injective Q).eq_iff
  simp only [calibratedHyperplaneVector, signedOctadVector, Pi.smul_apply, smul_eq_mul,
    xOctad_octad_apply, hh, mul_ite, mul_one, mul_zero]
  rfl

theorem octadicRoot_octad_coefficient {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    octadicRoot Q χ (.inr O) =
      (theta / 2 * parkerScalarSign Q.octadLift.val.2) *
        parkerScalarSign (χ (octadShortenedOne O)) := by
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  simp only [octadicRoot, Pi.smul_apply, Pi.add_apply, Finset.sum_apply,
    octadicAxisPart_octad_apply, calibratedHyperplaneVector_at_octad, smul_eq_mul,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero, signedOctadVector,
    xOctad_octad_apply, ho, ite_true, mul_one]
  ring

theorem octadicRoot_hyperplane_coefficient {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (b : OctadShortenedHyperplane O) :
    octadicRoot Q χ (.inr (signedOctadSupport (calibratedHyperplaneLift Q b))) =
      ((1 / 2 : Scalar) * parkerScalarSign (Q.parkerSection.sign b.val)) *
        parkerScalarSign (χ b.val) := by
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  simp only [octadicRoot, Pi.smul_apply, Pi.add_apply, Finset.sum_apply,
    octadicAxisPart_octad_apply, calibratedHyperplaneVector_at_support, smul_eq_mul,
    signedOctadVector, xOctad_octad_apply, ho,
    ite_eq_right (calibratedHyperplaneSupport_ne_octad Q b), mul_zero, zero_add,
    mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- All 32 characters give distinct actual vectors, detected by their retained
octad coordinates; no quotient or abstract phase labels are substituted. -/
theorem octadicRoot_injective {O : Octad} (Q : OctadCalibration O) :
    Function.Injective (octadicRoot Q) := by
  intro χ ψ h
  apply LinearMap.ext
  intro b
  by_cases hb : b = 0
  · simp [hb]
  · by_cases hX : b = octadShortenedOne O
    · subst b
      have he := congrFun h (.inr O)
      rw [octadicRoot_octad_coefficient, octadicRoot_octad_coefficient] at he
      apply parkerScalarSign_injective
      exact mul_left_cancel₀ (mul_ne_zero (div_ne_zero theta_ne_zero (by norm_num))
        (parkerScalarSign_ne_zero _)) he
    · let c : OctadShortenedHyperplane O := ⟨b, hb, hX⟩
      have he := congrFun h (.inr (signedOctadSupport (calibratedHyperplaneLift Q c)))
      rw [octadicRoot_hyperplane_coefficient, octadicRoot_hyperplane_coefficient] at he
      apply parkerScalarSign_injective
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (1 / 2 : Scalar) ≠ 0)
        (parkerScalarSign_ne_zero _)) he

def octadicRootFibre {O : Octad} (Q : OctadCalibration O) : Set Coordinates := Set.range (octadicRoot Q)

theorem octadicRootFibre_card {O : Octad} (Q : OctadCalibration O) :
    Nat.card (octadicRootFibre Q) = 32 := by
  unfold octadicRootFibre
  rw [← Nat.card_congr (Equiv.ofInjective (octadicRoot Q) (octadicRoot_injective Q))]
  exact octadCharacters_card O

theorem octadicRootFibre_choice_independent {O : Octad} (Q R : OctadCalibration O) :
    octadicRootFibre Q = octadicRootFibre R := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨χ, rfl⟩
    exact ⟨χ + octadCalibrationDifference R Q, (octadicRoot_change R Q χ).symm⟩
  · rintro ⟨χ, rfl⟩
    exact ⟨χ + octadCalibrationDifference Q R, (octadicRoot_change Q R χ).symm⟩

end Atlas.Fischer

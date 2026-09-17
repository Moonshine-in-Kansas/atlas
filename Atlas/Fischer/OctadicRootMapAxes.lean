import Atlas.Fischer.OctadicRootEquations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadicRoot_axis_coefficient {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (i : Omega) :
    octadicRoot Q χ (.inl i) = if i ∈ O.val then -1 / 2 else 1 / 2 := by
  simp only [octadicRoot, Pi.smul_apply, Pi.add_apply, Finset.sum_apply,
    octadicAxisPart_axis_apply, calibratedHyperplaneVector, signedOctadVector_axis_apply,
    smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
  split_ifs <;> ring

theorem hermitian_octadicRoot_u {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (i : Omega) :
    hermitian (octadicRoot Q χ) (u i) = if i ∈ O.val then -1 / 16 else 1 / 16 := by
  rw [← hermitian_star]
  change star (hermitian (coordinateVector (.inl i)) (octadicRoot Q χ)) = _
  rw [hermitian_coordinateVector_left, octadicRoot_axis_coefficient]
  split_ifs <;> norm_num [coordinateWeight]

theorem product_u_octadAxisSum_inside (O : Octad) (i : Omega) (hi : i ∈ O.val) :
    product (u i) (octadAxisSum O) =
      (1 / 16 : Scalar) • axisSum + (1 / 8 : Scalar) • octadAxisSum O := by
  rw [octadAxisSum, product_sum_right]
  simp only [product_u]
  exact axisBasisProduct_octad_total O i hi

theorem product_u_octadAxisSum_outside (O : Octad) (i : Omega) (hi : i ∉ O.val) :
    product (u i) (octadAxisSum O) =
      (-1 / 16 : Scalar) • axisSum + u i + (1 / 8 : Scalar) • octadAxisSum O := by
  rw [octadAxisSum, product_sum_right]
  simp only [product_u, axisBasisProduct_normalForm, ← Finset.smul_sum,
    Finset.sum_add_distrib, Finset.sum_ite_eq, hi, ite_false, Finset.sum_const,
    octad_size O.val O.property]
  change (1 / 128 : Scalar) • ((8 : ℕ) • -axisSum +
    (16 : Scalar) • ((8 : ℕ) • u i) + (16 : Scalar) • octadAxisSum O + 0) =
    (-1 / 16 : Scalar) • axisSum + u i + (1 / 8 : Scalar) • octadAxisSum O
  module

theorem product_u_octadicAxis_inside (O : Octad) (i : Omega) (hi : i ∈ O.val) :
    product (u i) (octadicAxisPart O) =
      (2 : Scalar) • u i - (1 / 16 : Scalar) • axisSum - (1 / 4 : Scalar) • octadAxisSum O := by
  rw [octadicAxisPart_eq, product_sub_right, product_smul_right, product_u_axisSum,
    product_u_octadAxisSum_inside O i hi]
  norm_num only [star_ofNat]
  module

theorem product_u_octadicAxis_outside (O : Octad) (i : Omega) (hi : i ∉ O.val) :
    product (u i) (octadicAxisPart O) =
      (3 / 16 : Scalar) • axisSum - (1 / 4 : Scalar) • octadAxisSum O := by
  rw [octadicAxisPart_eq, product_sub_right, product_smul_right, product_u_axisSum,
    product_u_octadAxisSum_outside O i hi]
  norm_num only [star_ofNat]
  module

theorem product_u_calibratedOctad {O : Octad} (Q : OctadCalibration O) (i : Omega) :
    product (u i) (signedOctadVector Q.octadLift) =
      (if i ∈ O.val then (3 / 16 : Scalar) else -1 / 16) • signedOctadVector Q.octadLift := by
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  rw [signedOctadVector, product_smul_right, parkerScalarSign_star, product_u_xOctad,
    axisOctadBasisProduct, ho]
  module

theorem product_u_calibratedHyperplane {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) (i : Omega) :
    product (u i) (calibratedHyperplaneVector Q b) =
      (if b.val.val.val i = 1 then (3 / 16 : Scalar) else -1 / 16) • calibratedHyperplaneVector Q b := by
  rw [calibratedHyperplaneVector, signedOctadVector, product_smul_right, parkerScalarSign_star,
    product_u_xOctad, axisOctadBasisProduct]
  simp only [calibratedHyperplaneSupport_mem]
  module

theorem product_u_hyperplanePart_inside {O : Octad} (Q : OctadCalibration O)
    (i : Omega) (hi : i ∈ O.val) :
    product (u i) (octadicHyperplanePart Q 0) = (-1 / 16 : Scalar) • octadicHyperplanePart Q 0 := by
  rw [octadicHyperplanePart_zero, product_sum_right]
  have hz (b : OctadShortenedHyperplane O) : b.val.val.val i = 0 :=
    (mem_octadShortenedCode O b.val.val).mp b.val.property i hi
  simp only [product_u_calibratedHyperplane, hz, zero_ne_one, ite_false, ← Finset.smul_sum]

theorem product_u_hyperplanePart_outside {O : Octad} (Q : OctadCalibration O)
    (i : OctadExterior O) :
    product (u i.val) (octadicHyperplanePart Q 0) =
      (1 / 16 : Scalar) • octadicHyperplanePart Q 0 -
        (1 / 8 : Scalar) • octadicHyperplanePart Q (octadEvaluation O i) := by
  rw [octadicHyperplanePart_zero, product_sum_right]
  simp only [product_u_calibratedHyperplane, octadicHyperplanePart, LinearMap.zero_apply,
    parkerScalarSign, ite_true, one_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  change (if b.val.val.val i.val = 1 then (3 / 16 : Scalar) else -1 / 16) •
    calibratedHyperplaneVector Q b = _
  have hb : b.val.val.val i.val = 0 ∨ b.val.val.val i.val = 1 := by
    have ht : ∀ t : Bit, t = 0 ∨ t = 1 := by decide
    exact ht _
  rcases hb with hb | hb <;>
    simp [octadEvaluation, hb] <;> module

/-- Source (5.10), obtained from the actual coordinate product and root map. -/
theorem rootMap_octadic_inside_axis {O : Octad} (Q : OctadCalibration O)
    (i : Omega) (hi : i ∈ O.val) :
    rootMap (octadicRoot Q 0) (u i) = u i - (3 / 16 : Scalar) • octadAxisSum O -
      (theta / 16) • signedOctadVector Q.octadLift := by
  rw [rootMap, hermitian_octadicRoot_u, ite_eq_left hi, octadicRoot_zero_formula,
    product_smul_right, product_add_right, product_add_right, product_u_octadicAxis_inside O i hi,
    product_smul_right, product_u_calibratedOctad, ite_eq_left hi,
    product_u_hyperplanePart_inside Q i hi, theta_conjugate, octadicAxisPart_eq]
  norm_num
  module

/-- Source (5.12), retaining the actual evaluation character of the exterior point. -/
theorem rootMap_octadic_outside_axis {O : Octad} (Q : OctadCalibration O)
    (i : OctadExterior O) :
    rootMap (octadicRoot Q 0) (u i.val) = (1 / 16 : Scalar) •
      (octadExteriorAxisSum O - octadicHyperplanePart Q (octadEvaluation O i)) := by
  rw [rootMap, hermitian_octadicRoot_u, ite_eq_right i.property, octadicRoot_zero_formula,
    product_smul_right, product_add_right, product_add_right,
    product_u_octadicAxis_outside O i.val i.property, product_smul_right,
    product_u_calibratedOctad, ite_eq_right i.property, product_u_hyperplanePart_outside Q i,
    theta_conjugate, octadicAxisPart_eq, ← octadAxisSum_add_exterior O]
  norm_num
  module

end Atlas.Fischer

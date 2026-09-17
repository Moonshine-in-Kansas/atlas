import Atlas.Fischer.OctadicAxisProducts
import Atlas.Fischer.OctadicNormCalculation
import Atlas.Fischer.BasicRootMaps

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem product_octadAxisSum_xOctad (O : Octad) :
    product (octadAxisSum O) (xOctad O) = (3 / 2 : Scalar) • xOctad O := by
  rw [octadAxisSum, product_sum_left]
  have ht (i : Omega) (hi : i ∈ O.val) : product (u i) (xOctad O) =
      (3 / 16 : Scalar) • xOctad O := by
    rw [product_u_xOctad, axisOctadBasisProduct, ite_eq_left hi]
  rw [Finset.sum_congr rfl ht, Finset.sum_const, octad_size O.val O.property]
  module

theorem product_octadAxisSum_xOctad_disjoint (O D : Octad) (hd : Disjoint O.val D.val) :
    product (octadAxisSum O) (xOctad D) = (-1 / 2 : Scalar) • xOctad D := by
  rw [octadAxisSum, product_sum_left]
  have ht (i : Omega) (hi : i ∈ O.val) : product (u i) (xOctad D) =
      (-1 / 16 : Scalar) • xOctad D := by
    rw [product_u_xOctad, axisOctadBasisProduct,
      ite_eq_right (fun hh => Finset.disjoint_left.mp hd hi hh)]
  rw [Finset.sum_congr rfl ht, Finset.sum_const, octad_size O.val O.property]
  module

theorem calibratedHyperplaneSupport_disjoint {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    Disjoint O.val (signedOctadSupport (calibratedHyperplaneLift Q b)).val := by
  rw [Finset.disjoint_left]
  intro i hi hb
  have hz := (mem_octadShortenedCode O b.val.val).mp b.val.property i hi
  change i ∈ support b.val.val.val at hb
  simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and, hz, ne_self_iff_false] using hb

theorem product_octadicAxisPart_octad {O : Octad} (Q : OctadCalibration O) :
    product (octadicAxisPart O) (signedOctadVector Q.octadLift) =
      (-5 / 2 : Scalar) • signedOctadVector Q.octadLift := by
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  rw [signedOctadVector, product_smul_right, parkerScalarSign_star, octadicAxisPart_eq,
    product_sub_left, product_smul_left, ho, product_comm axisSum (xOctad O),
    product_xOctad_axisSum, product_octadAxisSum_xOctad]
  norm_num only [star_ofNat]
  module

/-- The second row of the octadic square table. -/
theorem product_octadicAxisPart_theta_octad {O : Octad} (Q : OctadCalibration O) :
    (2 : Scalar) • product (octadicAxisPart O) (theta • signedOctadVector Q.octadLift) =
      (5 * theta) • signedOctadVector Q.octadLift := by
  rw [product_smul_right, theta_conjugate, product_octadicAxisPart_octad]
  module

theorem product_octadicAxisPart_hyperplane {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    product (octadicAxisPart O) (calibratedHyperplaneVector Q b) =
      (3 / 2 : Scalar) • calibratedHyperplaneVector Q b := by
  rw [calibratedHyperplaneVector, signedOctadVector, product_smul_right, parkerScalarSign_star,
    octadicAxisPart_eq, product_sub_left, product_smul_left,
    product_comm axisSum (xOctad _), product_xOctad_axisSum,
    product_octadAxisSum_xOctad_disjoint O _ (calibratedHyperplaneSupport_disjoint Q b)]
  norm_num only [star_ofNat]
  module

/-- The third row of the octadic square table, valid for every character. -/
theorem product_octadicAxisPart_hyperplanePart {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) :
    (2 : Scalar) • product (octadicAxisPart O) (octadicHyperplanePart Q χ) =
      (3 : Scalar) • octadicHyperplanePart Q χ := by
  rw [octadicHyperplanePart, product_sum_right]
  simp only [product_smul_right, parkerScalarSign_star, product_octadicAxisPart_hyperplane,
    smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  module

theorem product_calibratedOctad_self {O : Octad} (Q : OctadCalibration O) :
    (2 : Scalar) • product (signedOctadVector Q.octadLift) (signedOctadVector Q.octadLift) =
      (3 : Scalar) • octadAxisSum O - octadExteriorAxisSum O := by
  have ho : signedOctadSupport Q.octadLift = O :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  simp only [signedOctadVector, product_smul_left, product_smul_right, parkerScalarSign_star,
    smul_smul, parkerScalarSign_square, one_smul, ho]
  exact product_octad_self O

/-- The fourth row of the octadic square table. -/
theorem product_theta_calibratedOctad_self {O : Octad} (Q : OctadCalibration O) :
    product (theta • signedOctadVector Q.octadLift) (theta • signedOctadVector Q.octadLift) =
      (-9 / 2 : Scalar) • octadAxisSum O + (3 / 2 : Scalar) • octadExteriorAxisSum O := by
  rw [product_smul_left, product_smul_right, theta_conjugate]
  have h := product_calibratedOctad_self Q
  have he : product (signedOctadVector Q.octadLift) (signedOctadVector Q.octadLift) =
      (1 / 2 : Scalar) • ((3 : Scalar) • octadAxisSum O - octadExteriorAxisSum O) := by
    rw [← h, smul_smul]
    norm_num
  rw [he, smul_smul, smul_smul]
  have hc : -theta * -theta * (1 / 2) = (-3 / 2 : Scalar) := by
    calc
      _ = theta ^ 2 / 2 := by ring
      _ = _ := by rw [theta_sq]
  rw [hc]
  module

end Atlas.Fischer

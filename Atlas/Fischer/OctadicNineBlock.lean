import Atlas.Fischer.OctadicRootMapOctad
import Atlas.Fischer.RootMapSubspaces

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem hermitian_u_octadAxisSum (O : Octad) (i : Omega) :
    hermitian (u i) (octadAxisSum O) = if i ∈ O.val then 1 / 8 else 0 := by
  simp only [octadAxisSum, hermitian_sum_right, hermitian_u, Finset.sum_ite_eq]

theorem hermitian_octadAxisSum_u (O : Octad) (i : Omega) :
    hermitian (octadAxisSum O) (u i) = if i ∈ O.val then 1 / 8 else 0 := by
  rw [← hermitian_star, hermitian_u_octadAxisSum]
  split_ifs <;> norm_num

theorem octadAxisSum_norm (O : Octad) : hermitian (octadAxisSum O) (octadAxisSum O) = 1 := by
  conv_lhs => lhs; rw [octadAxisSum]
  rw [hermitian_sum_left]
  have hh (i : Omega) (hi : i ∈ O.val) : hermitian (u i) (octadAxisSum O) = (1 / 8 : Scalar) := by
    rw [hermitian_u_octadAxisSum, ite_eq_left hi]
  rw [Finset.sum_congr rfl hh, Finset.sum_const, octad_size O.val O.property]
  norm_num

theorem hermitian_u_signedOctad (i : Omega) (d : SignedOctad) :
    hermitian (u i) (signedOctadVector d) = 0 := by
  simp only [signedOctadVector, hermitian_smul_right, hermitian_u_xOctad, mul_zero]

theorem hermitian_signedOctad_u (d : SignedOctad) (i : Omega) :
    hermitian (signedOctadVector d) (u i) = 0 := by
  rw [← hermitian_star, hermitian_u_signedOctad, star_zero]

theorem hermitian_octadAxisSum_signedOctad (O : Octad) (d : SignedOctad) :
    hermitian (octadAxisSum O) (signedOctadVector d) = 0 := by
  simp only [octadAxisSum, hermitian_sum_left, hermitian_u_signedOctad, Finset.sum_const_zero]

theorem hermitian_signedOctad_octadAxisSum (d : SignedOctad) (O : Octad) :
    hermitian (signedOctadVector d) (octadAxisSum O) = 0 := by
  rw [← hermitian_star, hermitian_octadAxisSum_signedOctad, star_zero]

theorem rootMap_octadic_inside_pairing {O : Octad} (Q : OctadCalibration O)
    (i j : Omega) (hi : i ∈ O.val) (hj : j ∈ O.val) :
    hermitian (rootMap (octadicRoot Q 0) (u i)) (rootMap (octadicRoot Q 0) (u j)) =
      star (hermitian (u i) (u j)) := by
  rw [rootMap_octadic_inside_axis Q i hi, rootMap_octadic_inside_axis Q j hj]
  simp only [hermitian_sub_left, hermitian_sub_right, hermitian_smul_left, hermitian_smul_right,
    hermitian_u_octadAxisSum, hermitian_octadAxisSum_u, ite_eq_left hi, ite_eq_left hj,
    hermitian_u_signedOctad, hermitian_signedOctad_u, hermitian_octadAxisSum_signedOctad,
    hermitian_signedOctad_octadAxisSum, octadAxisSum_norm, signedOctadVector_norm,
    mul_zero, zero_mul, mul_one, hermitian_u]
  split_ifs <;> simp only [star_div₀, star_ofNat, star_one, star_zero, theta_conjugate] <;>
    ring_nf <;> norm_num [theta_sq]

theorem rootMap_octadic_inside_octad_pairing {O : Octad} (Q : OctadCalibration O)
    (i : Omega) (hi : i ∈ O.val) :
    hermitian (rootMap (octadicRoot Q 0) (u i))
      (rootMap (octadicRoot Q 0) (signedOctadVector Q.octadLift)) = 0 := by
  rw [rootMap_octadic_inside_axis Q i hi, rootMap_octadic_octad]
  simp only [hermitian_sub_left, hermitian_sub_right, hermitian_smul_left, hermitian_smul_right,
    hermitian_u_octadAxisSum, ite_eq_left hi, hermitian_u_signedOctad,
    hermitian_octadAxisSum_signedOctad, hermitian_signedOctad_octadAxisSum,
    octadAxisSum_norm, signedOctadVector_norm, mul_zero, zero_mul, mul_one,
    star_div₀, star_neg, star_ofNat, star_one, theta_conjugate]
  ring

theorem rootMap_octadic_octad_norm {O : Octad} (Q : OctadCalibration O) :
    hermitian (rootMap (octadicRoot Q 0) (signedOctadVector Q.octadLift))
      (rootMap (octadicRoot Q 0) (signedOctadVector Q.octadLift)) = 1 := by
  rw [rootMap_octadic_octad]
  simp only [hermitian_sub_left, hermitian_sub_right, hermitian_smul_left, hermitian_smul_right,
    hermitian_octadAxisSum_signedOctad, hermitian_signedOctad_octadAxisSum,
    octadAxisSum_norm, signedOctadVector_norm, mul_zero, zero_mul, mul_one,
    star_div₀, star_neg, star_ofNat, star_one, theta_conjugate]
  ring_nf
  norm_num [theta_sq]

def octadicNineGenerators {O : Octad} (Q : OctadCalibration O) : Set Coordinates :=
  Set.range (fun i : {i : Omega // i ∈ O.val} => u i.val) ∪ {signedOctadVector Q.octadLift}

def octadicNineSpace {O : Octad} (Q : OctadCalibration O) : Submodule Scalar Coordinates :=
  Submodule.span Scalar (octadicNineGenerators Q)

theorem rootMap_octadic_nine_invariant {O : Octad} (Q : OctadCalibration O) :
    Set.MapsTo (rootMap (octadicRoot Q 0)) (octadicNineSpace Q) (octadicNineSpace Q) := by
  have hu (i : Omega) (hi : i ∈ O.val) : u i ∈ octadicNineSpace Q :=
    Submodule.subset_span (Or.inl ⟨⟨i, hi⟩, rfl⟩)
  have ho : signedOctadVector Q.octadLift ∈ octadicNineSpace Q :=
    Submodule.subset_span (Or.inr rfl)
  have hs : octadAxisSum O ∈ octadicNineSpace Q := (octadicNineSpace Q).sum_mem hu
  apply rootMap_invariant_span
  intro x hx
  rcases hx with ⟨i, rfl⟩ | rfl
  · rw [rootMap_octadic_inside_axis Q i.val i.property]
    exact (octadicNineSpace Q).sub_mem ((octadicNineSpace Q).sub_mem (hu _ i.property)
      ((octadicNineSpace Q).smul_mem _ hs)) ((octadicNineSpace Q).smul_mem _ ho)
  · rw [rootMap_octadic_octad]
    exact (octadicNineSpace Q).sub_mem ((octadicNineSpace Q).smul_mem _ hs)
      ((octadicNineSpace Q).smul_mem _ ho)

theorem rootMap_octadic_nine_antiunitary {O : Octad} (Q : OctadCalibration O) :
    RootMapAntiunitaryOn (octadicRoot Q 0) (octadicNineSpace Q) := by
  apply rootMap_antiunitary_span
  intro x hx y hy
  rcases hx with ⟨i, rfl⟩ | rfl <;> rcases hy with ⟨j, rfl⟩ | rfl
  · exact rootMap_octadic_inside_pairing Q i.val j.val i.property j.property
  · rw [rootMap_octadic_inside_octad_pairing Q i.val i.property, hermitian_u_signedOctad, star_zero]
  · rw [← hermitian_star, rootMap_octadic_inside_octad_pairing Q j.val j.property,
      hermitian_signedOctad_u, star_zero]
  · rw [rootMap_octadic_octad_norm, signedOctadVector_norm, star_one]

theorem rootMap_octadic_nine_involutive {O : Octad} (Q : OctadCalibration O)
    (x : Coordinates) (hx : x ∈ octadicNineSpace Q) :
    rootMap (octadicRoot Q 0) (rootMap (octadicRoot Q 0) x) = x :=
  rootMap_involutive_on_of_antiunitaryOn _ _ (rootMap_octadic_nine_invariant Q)
    (rootMap_octadic_nine_antiunitary Q) x hx

end Atlas.Fischer

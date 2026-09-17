import Atlas.Fischer.CubicPointBlockQuadratic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The retained point cubic as an explicit bilinear form in its last two slots. -/
theorem cubicPointPattern_bilinear (i : Omega) (v w : Omega → Scalar) :
    (∑ a : Omega, ∑ b : Omega, cubicPointPattern i a b * v a * w b) =
      -(∑ a, v a) * (∑ a, w a) +
        16 * (v i * (∑ a, w a) + w i * (∑ a, v a)) +
        16 * (∑ a, v a * w a) - 128 * v i * w i := by
  classical
  simp only [cubicPointPattern_normalForm, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_ite_irrel, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_mul] <;> ring

/-- Mixed actual octad-incidence vectors in the point cubic. -/
theorem coordinateCubic_point_octad_bilinear (p : Omega) (D E : Octad) :
    (∑ a : Omega, ∑ b : Omega, coordinateCubic (.inl p) (.inl a) (.inl b) *
      cubicPointOctadIncidence a D * cubicPointOctadIncidence b E) =
      (-64 + 128 * (cubicPointOctadIncidence p D + cubicPointOctadIncidence p E) +
        16 * (∑ a : Omega, cubicPointOctadIncidence a D * cubicPointOctadIncidence a E) -
        128 * cubicPointOctadIncidence p D * cubicPointOctadIncidence p E) / 1024 := by
  simp_rw [coordinateCubic_points, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [cubicPointPattern_bilinear, cubicPointOctadIncidence_sum,
    cubicPointOctadIncidence_sum]
  ring

end Atlas.Fischer

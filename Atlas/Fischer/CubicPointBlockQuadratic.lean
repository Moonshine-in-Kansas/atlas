import Atlas.Fischer.CubicSlicePointPattern
import Atlas.Fischer.CubicSliceOctadIncidence
import Atlas.Fischer.CubicTriangleIncidence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The point-block quadratic form is a sum of diagonal and rank-one pieces. -/
theorem cubicPointPattern_quadratic (i : Omega) (v : Omega → Scalar) :
    (∑ a : Omega, ∑ b : Omega, cubicPointPattern i a b * v a * v b) =
      -(∑ a, v a)^2 + 32 * v i * (∑ a, v a) +
        16 * (∑ a, v a * v a) - 128 * v i * v i := by
  classical
  simp only [cubicPointPattern_normalForm, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_ite_irrel, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_mul] <;> ring

/-- The actual octad-incidence vector has the same quadratic value in every point block. -/
theorem cubicPointPattern_octad_quadratic (i : Omega) (D : Octad) :
    (∑ a : Omega, ∑ b : Omega, cubicPointPattern i a b *
      cubicPointOctadIncidence a D * cubicPointOctadIncidence b D) = 960 := by
  rw [cubicPointPattern_quadratic, cubicPointOctadIncidence_sum]
  have hs := cubicPointOctadIncidence_square_sum D
  rw [hs]
  by_cases hi : i ∈ D.val <;> norm_num [cubicPointOctadIncidence, hi]

/-- The same identity in the retained, unnormalized E-coordinate cubic. -/
theorem coordinateCubic_point_octad_quadratic (i : Omega) (D : Octad) :
    (∑ a : Omega, ∑ b : Omega, coordinateCubic (.inl i) (.inl a) (.inl b) *
      cubicPointOctadIncidence a D * cubicPointOctadIncidence b D) = 15 / 16 := by
  simp_rw [coordinateCubic_points, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [cubicPointPattern_octad_quadratic]
  norm_num

end Atlas.Fischer

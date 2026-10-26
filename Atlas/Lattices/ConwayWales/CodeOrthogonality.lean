import Atlas.Lattices.ConwayWales.FrameCode
import Atlas.Lattices.ConwayWales.Evenness

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Atlas.ConwayWales

def integerDot (z w : IntegerCoordinates) : ℤ := ∑ i, z i * w i

theorem halfEmbedding_real_pair (z w : IntegerCoordinates) :
    (hermitian (halfEmbedding z) (halfEmbedding w)).re = (integerDot z w : ℝ) / 4 := by
  unfold integerDot hermitian
  simp only [Fintype.sum_prod_type, Int.cast_sum, Int.cast_mul, Complex.re_sum,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Fin.sum_univ_succ, Finset.sum_div, Fin.val_zero, Fin.val_succ]
  simp only [halfEmbedding, Pi.smul_apply, integerEmbedding, dagger,
    Quaternion.re_mul, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
    Quaternion.imK_smul, smul_eq_mul, gaussian_coordinate_formula]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  norm_num
  ring_nf
  rfl

/-- Self-orthogonality of integer lifts follows from integrality of the original lattice. -/
theorem code_integer_dot_divisible (z w : IntegerCoordinates)
    (hz : modFour z ∈ frameCode) (hw : modFour w ∈ frameCode) : 4 ∣ integerDot z w := by
  obtain ⟨g,hg⟩ := seedLattice_gaussian_integral (halfEmbedding z) (halfEmbedding w)
    ((halfEmbedding_mem_iff_code z).mpr hz) ((halfEmbedding_mem_iff_code w).mpr hw)
  have hr := congrArg Complex.re hg
  rw [← GaussianInt.intCast_re, halfEmbedding_real_pair] at hr
  refine ⟨g.re, ?_⟩
  have hreal : (integerDot z w : ℝ) = 4 * (g.re : ℝ) := by linarith
  exact_mod_cast hreal

/-- The standard dot product over Z/4 vanishes on every pair of actual codewords. -/
theorem frameCode_self_orthogonal (x y : FrameCodeSpace)
    (hx : x ∈ frameCode) (hy : y ∈ frameCode) : ∑ i, x i * y i = 0 := by
  obtain ⟨z,hz,rfl⟩ := hx
  obtain ⟨w,hw,rfl⟩ := hy
  have hd := code_integer_dot_divisible z w
    ((halfEmbedding_mem_iff_code z).mp hz) ((halfEmbedding_mem_iff_code w).mp hw)
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd (integerDot z w) 4).mpr hd
  simpa only [integerDot, Int.cast_sum, Int.cast_mul, modFour] using hc

/-- Every integer lift of a codeword has squared Euclidean norm divisible by eight. -/
theorem code_integer_norm_divisible (z : IntegerCoordinates) (hz : modFour z ∈ frameCode) :
    8 ∣ integerDot z z := by
  obtain ⟨n,hn⟩ := seedLattice_even (halfEmbedding z) ((halfEmbedding_mem_iff_code z).mpr hz)
  rw [halfEmbedding_real_pair] at hn
  refine ⟨n, ?_⟩
  have hreal : (integerDot z z : ℝ) = 8 * (n : ℝ) := by linarith
  exact_mod_cast hreal

end Atlas.ConwayWales

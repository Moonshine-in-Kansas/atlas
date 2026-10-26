import Atlas.Lattices.ConwayWales.Integrality

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Atlas.ConwayWales

theorem rowPair_right_basis (x y : Q) (u : Fin 4) :
    rowPair (x * quaternionBasis u) (y * quaternionBasis u) = rowPair x y := by
  fin_cases u <;> simp [rowPair, dagger, quaternionBasis, j, k, l] <;> ring

theorem hermitian_right_basis (v w : Space) (u : Fin 4) :
    hermitian (fun r => v r * quaternionBasis u) (fun r => w r * quaternionBasis u) =
      hermitian v w := by
  apply Finset.sum_congr rfl
  intro r _
  exact rowPair_right_basis (v r) (w r) u

theorem hermitian_translate_same (d : Row) (v w : Space) :
    hermitian (translate d v) (translate d w) = hermitian v w := by
  rw [hermitian_eq_quaternionPair_re, quaternionPair_translate, sub_self]
  change (quaternionPair v (fun r => w (r - 0))).re = hermitian v w
  simp only [sub_zero, ← hermitian_eq_quaternionPair_re]

theorem seedGenerator_norm (t : Fin 3) (d : Row) (u : Fin 4) :
    hermitian (seedGenerator t d u) (seedGenerator t d u) = 4 := by
  fin_cases t
  · fin_cases u <;> simp [hermitian, seedGenerator, quaternionBasis, j, k, l,
      dagger, apply_ite, mul_ite, ite_mul] <;> norm_num
  · change hermitian (fun r => translate d a r * quaternionBasis u)
      (fun r => translate d a r * quaternionBasis u) = 4
    rw [hermitian_right_basis, hermitian_translate_same, norm_a]
  · change hermitian (fun r => translate d b r * quaternionBasis u)
      (fun r => translate d b r * quaternionBasis u) = 4
    rw [hermitian_right_basis, hermitian_translate_same, norm_b]

theorem hermitian_add_left (v w z : Space) :
    hermitian (v+w) z = hermitian v z + hermitian w z := by
  simp only [hermitian_eq_quaternionPair_re, quaternionPair_add_left, Quaternion.re_add]

theorem hermitian_add_right (v w z : Space) :
    hermitian v (w+z) = hermitian v w + hermitian v z := by
  simp only [hermitian_eq_quaternionPair_re, quaternionPair_add_right, Quaternion.re_add]

theorem hermitian_swap (v w : Space) : star (hermitian v w) = hermitian w v := by
  rw [hermitian_eq_quaternionPair_re, hermitian_eq_quaternionPair_re,
    ← quaternionPair_swap]
  simp [dagger]

theorem hermitian_real_add_self (v w : Space) :
    (hermitian (v+w) (v+w)).re = (hermitian v v).re + (hermitian w w).re +
      2 * (hermitian v w).re := by
  have hs : (hermitian w v).re = (hermitian v w).re := by
    rw [← hermitian_swap]
    rfl
  rw [hermitian_add_left, hermitian_add_right, hermitian_add_right]
  simp only [Complex.add_re, hs]
  ring

theorem hermitian_real_gaussian_smul (z : GaussianInt) (v : Space) :
    (hermitian (GaussianInt.toComplex z • v) (GaussianInt.toComplex z • v)).re =
      ((z.re : ℝ)^2 + (z.im : ℝ)^2) * (hermitian v v).re := by
  simp only [hermitian_eq_quaternionPair_re, quaternionPair_smul_left,
    quaternionPair_smul_right, Quaternion.re_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im, pow_two]
  ring

/-- Even real norm, stated with an actual integral witness. -/
def EvenRealNorm (v : Space) : Prop := ∃ n : ℤ, (hermitian v v).re = 2 * (n : ℝ)

theorem seedLattice_even (v : Space) (hv : v ∈ seedLattice) : EvenRealNorm v := by
  change v ∈ Submodule.span GaussianInt _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨t,d,u⟩,rfl⟩ := hv
    refine ⟨2, ?_⟩
    rw [seedGenerator_norm]
    norm_num
  | zero =>
    refine ⟨0, ?_⟩
    simp [hermitian, dagger]
  | add x y hx hy ihx ihy =>
    obtain ⟨m,hm⟩ := ihx
    obtain ⟨n,hn⟩ := ihy
    obtain ⟨z,hz⟩ := seedLattice_gaussian_integral x y hx hy
    refine ⟨m+n+z.re, ?_⟩
    rw [hermitian_real_add_self, hm, hn, ← hz]
    rw [← GaussianInt.intCast_re]
    push_cast
    ring
  | smul z x hx ih =>
    obtain ⟨n,hn⟩ := ih
    refine ⟨(z.re^2+z.im^2)*n, ?_⟩
    change (hermitian (GaussianInt.toComplex z • x) (GaussianInt.toComplex z • x)).re = _
    rw [hermitian_real_gaussian_smul, hn]
    push_cast
    ring

end Atlas.ConwayWales

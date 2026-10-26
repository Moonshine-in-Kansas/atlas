import Atlas.Lattices.ConwayWales.GaussianCoordinates

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Atlas.ConwayWales

def daggerAddHom : Q →+ Q where
  toFun := dagger
  map_zero' := by ext <;> simp [dagger]
  map_add' := dagger_add

theorem dagger_sum {ι : Type*} (s : Finset ι) (v : ι → Q) :
    dagger (∑ i ∈ s, v i) = ∑ i ∈ s, dagger (v i) := map_sum daggerAddHom v s

def quaternionPair (v w : Space) : Q := ∑ r, dagger (v r) * w r

theorem quaternionPair_add_left (v w z : Space) :
    quaternionPair (v + w) z = quaternionPair v z + quaternionPair w z := by
  simp [quaternionPair, add_mul, Finset.sum_add_distrib]

theorem quaternionPair_add_right (v w z : Space) :
    quaternionPair v (w + z) = quaternionPair v w + quaternionPair v z := by
  simp [quaternionPair, mul_add, Finset.sum_add_distrib]

theorem quaternionPair_smul_left (z : ℂ) (v w : Space) :
    quaternionPair (z • v) w = star z • quaternionPair v w := by
  simp [quaternionPair, smul_mul_assoc, Finset.smul_sum]

theorem quaternionPair_smul_right (z : ℂ) (v w : Space) :
    quaternionPair v (z • w) = z • quaternionPair v w := by
  simp [quaternionPair, mul_smul_comm, Finset.smul_sum]

theorem quaternionPair_swap (v w : Space) :
    dagger (quaternionPair v w) = quaternionPair w v := by
  simp [quaternionPair, dagger_sum, dagger_mul, dagger_dagger]

theorem quaternionPair_right_multiples (v w : Space) (u z : Q) :
    quaternionPair (fun r => v r * u) (fun r => w r * z) =
      dagger u * quaternionPair v w * z := by
  simp [quaternionPair, dagger_mul, mul_assoc, Finset.mul_sum, Finset.sum_mul]

theorem quaternionPair_translate (d e : Row) (v w : Space) :
    quaternionPair (translate d v) (translate e w) =
      quaternionPair v (translate (e - d) w) := by
  unfold quaternionPair translate
  apply Fintype.sum_bijective (fun r : Row => r - d) (Equiv.subRight d).bijective
  intro r
  congr 2
  abel

theorem quaternionPair_convolution_adjoint (v w : Space) :
    quaternionPair (convolution v) w = quaternionPair v (convolution w) := by
  simp only [quaternionPair, convolution, dagger_smul, dagger_sum, Finset.sum_mul,
    Finset.mul_sum, mul_smul_comm, smul_mul_assoc, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  rw [dagger_mul, coefficient_self_adjoint, mul_assoc, add_comm r s]
  norm_num

theorem quaternionPair_convolution (v w : Space) :
    quaternionPair (convolution v) (convolution w) = quaternionPair v w := by
  rw [quaternionPair_convolution_adjoint, convolution_involutive w]

theorem gaussianOrder_dagger {q : Q} (hq : q ∈ gaussianOrder) : dagger q ∈ gaussianOrder := by
  rcases hq with ⟨h0,h1,h2,h3⟩
  exact ⟨gaussian_star h0, gaussianIntegers.neg_mem (gaussian_star h1),
    gaussianIntegers.neg_mem (gaussian_star h2), gaussianIntegers.neg_mem (gaussian_star h3)⟩

end Atlas.ConwayWales

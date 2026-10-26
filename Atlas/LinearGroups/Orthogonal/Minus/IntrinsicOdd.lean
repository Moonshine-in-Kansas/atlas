import Atlas.LinearGroups.Orthogonal.Minus.WittFrame
import Atlas.LinearGroups.Orthogonal.IntrinsicKernelIdentification
import Atlas.LinearGroups.Orthogonal.EvenDReflectionIdentification

/-! Intrinsic-kernel interfaces for the actual minus space of Witt index at least two. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem elementary_eq_intrinsic_kernel (hdeg : Module.finrank F K = 2) (n : ℕ)
    (h2 : (2 : F) ≠ 0) :
    E hdeg (n+2) = specialSubgroup (form hdeg (n+2)) ⊓
      (spinorNorm (form hdeg (n+2)) (polar_nondegenerate hdeg _) h2).ker :=
  elementary_eq_intrinsicKernel _ (wittTwoFrame hdeg n) (polar_nondegenerate hdeg _) h2

def elementarySpinorEquiv (hdeg : Module.finrank F K = 2) (n : ℕ)
    (h2 : (2 : F) ≠ 0) :
    E hdeg (n+2) ≃* specialSpinorKernel (form hdeg (n+2))
      (polar_nondegenerate hdeg _) h2 :=
  elementarySpecialSpinorEquiv _ (wittTwoFrame hdeg n) (polar_nondegenerate hdeg _) h2

theorem elementary_index_odd (hdeg : Module.finrank F K = 2) (n : ℕ)
    (h2 : (2 : F) ≠ 0) : (E hdeg (n+2)).index = 4 := by
  rw [elementary_eq_intrinsic_kernel hdeg n h2, ← determinantSpinor_kernel]
  exact determinantSpinor_kernel_index _ (wittTwoFrame hdeg n)
    (polar_nondegenerate hdeg _) h2

theorem evenReflection_le_elementary [CharP F 2] [PerfectRing F 2]
    (hdeg : Module.finrank F K = 2) (n : ℕ) :
    evenReflectionSubgroup (form hdeg (n+2)) ≤ E hdeg (n+2) :=
  evenReflection_le_elementary_char_two _ (wittTwoFrame hdeg n)
    (polar_nondegenerate hdeg _)

end Atlas.Orthogonal.Minus

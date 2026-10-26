import Atlas.Comparisons.Exceptional.E6.BinaryMinus
import Atlas.Comparisons.Exceptional.E6.BinaryReflectionImage
import Atlas.LinearGroups.Orthogonal.ReflectionTransport
import Atlas.LinearGroups.Orthogonal.Minus.ReflectionGeneration

/-! Binary Weyl reduction is onto the full minus orthogonal group.
This uses actual reflection generation, not equality with a target order. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Atlas.Orthogonal
variable {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
variable (hdeg : Module.finrank (ZMod 2) K = 2)
include hdeg

theorem binary_reflection_generation : reflectionSubgroup (form (ZMod 2)) = ⊤ :=
  reflectionSubgroup_eq_top_of_isometry (binaryMinusIsometry hdeg)
    (Minus.reflectionSubgroup_eq_top_of_two_le hdeg 2 (by decide))

theorem intoBinaryOrthogonal_surjective : Function.Surjective intoBinaryOrthogonal := by
  have hr := binary_reflectionSubgroup_le_range
  rw [binary_reflection_generation hdeg] at hr
  have ht : intoBinaryOrthogonal.range = ⊤ := top_unique hr
  exact MonoidHom.range_eq_top.mp ht

/-- Integral Weyl elements and all binary E6 isometries are the same group through reduction. -/
def binaryWeylEquiv : IntegralWeyl ≃* isometrySubgroup (form (ZMod 2)) :=
  MulEquiv.ofBijective intoBinaryOrthogonal
    ⟨intoBinaryOrthogonal_injective,intoBinaryOrthogonal_surjective hdeg⟩

/-- Full Weyl group identified with the existing full minus norm-plane group. -/
def weylMinusEquiv : IntegralWeyl ≃* Minus.O hdeg 2 :=
  (binaryWeylEquiv hdeg).trans (binaryMinusOrthogonalEquiv hdeg)

end Atlas.Comparisons.E6Lattice

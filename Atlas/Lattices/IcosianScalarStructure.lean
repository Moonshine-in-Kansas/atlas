import Atlas.Lattices.IcosianHermitianIdentities
import Atlas.Algebra.IcosianOrderBasis

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators Quaternion QuadraticAlgebra

def icosianRightMulLinear (a : IcosianQuaternion) : Module.End ℚ IcosianRationalCoordinates where
  toFun x := icosianRightMul x a
  map_add' x y := by funext j; exact add_mul _ _ _
  map_smul' r x := by funext j; exact smul_mul_assoc r (x j) a

/-- The weighted rational pairing and right-scalar linearity recover the complete
quaternion-valued Hermitian form. -/
theorem icosianHermitian_of_bilinear_and_right_linear
    (f : IcosianRationalCoordinates → IcosianRationalCoordinates)
    (hf : ∀ x y,icosianBilinear (f x) (f y)=icosianBilinear x y)
    (hl : ∀ a x,f (icosianRightMul x a)=icosianRightMul (f x) a) :
    ∀ x y,icosianHermitian (f x) (f y)=icosianHermitian x y := by
  intro x y
  apply icosianFunctional_pairing_ext
  intro a
  rw [icosianFunctional_mul_comm a,icosianFunctional_mul_comm a]
  have h := hf x (icosianRightMul y a)
  rw [hl] at h
  simp only [icosianBilinear,icosianHermitian_rightMul_right] at h
  linarith

end Atlas.Lattices

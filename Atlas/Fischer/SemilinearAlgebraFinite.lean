import Atlas.Fischer.RayKernelScalarSubgroup
import Mathlib.GroupTheory.QuotientGroup.Finite

noncomputable section
namespace Atlas.Fischer

/-- Finiteness of the actual full semilinear algebra group, derived only after
identifying the kernel of its finite ray action with the cubic scalar group. -/
theorem semilinearAlgebraAutomorphism_finite : Finite SemilinearAlgebraAutomorphism := by
  letI : Finite Mu3 := Nat.finite_of_card_ne_zero (by rw [mu3_card]; decide)
  letI : Fintype Mu3 := Fintype.ofFinite _
  letI : Finite DisplayedReflectingRay :=
    Nat.finite_of_card_ne_zero (by rw [displayedReflectingRay_card]; decide)
  letI : Fintype DisplayedReflectingRay := Fintype.ofFinite _
  letI : Fintype SemilinearAlgebraAutomorphism := Group.fintypeOfKerEqRange
    scalarAlgebraRepresentation semilinearDisplayedRayAction semilinearRayKernel_eq_scalar_range
  infer_instance

end Atlas.Fischer

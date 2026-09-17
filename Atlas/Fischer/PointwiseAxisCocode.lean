import Atlas.Fischer.RayKernelScalarSubgroup
import Atlas.Fischer.ProductTraceCocode
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Lattice

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Fixing the actual point axes fixes their basic reflecting combinations. -/
theorem pointwiseAxis_fixes_basic (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (i : Omega) : e.val (basicAxis i)=basicAxis i := by
  change productTraceAlgebraEquiv e (basicAxis i)=basicAxis i
  rw [basicAxis_eq, map_sub, map_smulₛₗ]
  have hs : productTraceAlgebraEquiv e axisSum=axisSum := by
    simp only [axisSum,map_sum]
    exact Finset.sum_congr rfl (fun j _ => he j)
  rw [hs]
  change axisSum - scalarParityAut (semilinearAlgebraParity e) 8 • e.val (u i)=_
  rw [map_ofNat,he]

/-- Pointwise axis stabilizers commute with every actual cocode operator,
using the verified generation by the basic reflections. -/
theorem pointwiseAxis_commutes_cocode (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (d : Multiplicative Cocode) (x : Coordinates) :
    e.val (cocodeCoordinateRepresentation d x)=cocodeCoordinateRepresentation d (e.val x) := by
  have hc : cocodeCoordinateRepresentation.range ≤ Subgroup.centralizer {e.val} := by
    rw [← cocodeReflections_generate]
    apply (Subgroup.closure_le _).2
    rintro p ⟨i,rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro f hf
    have hf0 : f=e.val := Set.mem_singleton_iff.mp hf
    subst f
    apply Equiv.ext
    intro y
    simp only [Equiv.Perm.mul_apply]
    rw [cocodeCoordinateRepresentation_generator,cocodeCoordinateRepresentation_generator]
    have h := semilinearAlgebra_rootMap e (basicAxis i) y
    rw [pointwiseAxis_fixes_basic e he i] at h
    exact h.symm
  have h := Subgroup.mem_centralizer_iff.mp (hc ⟨d,rfl⟩) e.val (Set.mem_singleton _)
  exact congrArg (fun f : Equiv.Perm Coordinates => f x) h

end Atlas.Fischer

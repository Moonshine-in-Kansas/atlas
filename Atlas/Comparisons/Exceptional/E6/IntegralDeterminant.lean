import Atlas.Comparisons.Exceptional.E6.MatrixReduction
import Mathlib.LinearAlgebra.Transvection.Basic

/-! The literal integral determinant character of the E6 Weyl group. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice

def integralDeterminant : IntegralWeyl →* ℤˣ :=
  LinearEquiv.det.comp
    ((Atlas.Orthogonal.isometrySubgroup (form ℤ)).subtype.comp (weyl ℤ).subtype)

/-- Determinant is computed by a rank-one transvection formula over the integers. -/
theorem simpleReflection_integralDeterminant (i : Fin 6) :
    integralDeterminant ⟨simpleReflection ℤ i,simpleReflection_mem ℤ i⟩ = -1 := by
  apply Units.ext
  change ((reflectionLinearEquiv ℤ i).det : ℤ) = -1
  rw [LinearEquiv.coe_det]
  let f : (Fin 6 → ℤ) →ₗ[ℤ] ℤ :=
    (LinearMap.proj i).comp ((reflectionLinearEquiv ℤ i).toLinearMap - LinearMap.id)
  have he : (reflectionLinearEquiv ℤ i).toLinearMap =
      LinearMap.transvection f (simpleRoot i) := by
    apply LinearMap.ext
    intro x
    funext j
    fin_cases i <;> fin_cases j <;>
      simp [f,reflectionLinearEquiv,reflection,simpleRoot,LinearMap.transvection.apply] <;> ring
  rw [he,LinearMap.transvection.det]
  fin_cases i <;> simp [f,reflectionLinearEquiv,reflection,simpleRoot]

/-- The positive Weyl subgroup uses the actual determinant, not a target-group predicate. -/
def positiveWeyl : Subgroup IntegralWeyl := integralDeterminant.ker

end Atlas.Comparisons.E6Lattice

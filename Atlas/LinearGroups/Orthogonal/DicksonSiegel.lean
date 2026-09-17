import Atlas.LinearAlgebra.QuadraticSiegelResidual
import Atlas.LinearGroups.Orthogonal.DicksonInvariant
import Atlas.LinearGroups.Orthogonal.SiegelSpinor

/-! # Every actual Siegel generator has zero intrinsic residual parity

This is independent of full orthogonal reflection generation and of multiplicativity
of the proposed full-group Dickson invariant. It applies in every characteristic.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

include hQ in
theorem dicksonValue_reflection_mul (a : V) (ha : Q a ≠ 0)
    (g : isometrySubgroup Q) :
    dicksonValue Q (reflectionElement Q a ha * g) = dicksonValue Q g + 1 := by
  have hi : isometryCarrierEquiv Q (reflectionElement Q a ha * g) =
      reflectedIsometry Q (isometryCarrierEquiv Q g) a ha := by
    apply DFunLike.ext
    intro x
    rfl
  change dicksonParity Q (isometryCarrierEquiv Q (reflectionElement Q a ha * g)) = _
  rw [hi]
  exact dicksonParity_reflection Q (isometryCarrierEquiv Q g) hQ a ha

include hQ in
theorem dicksonValue_reflection (a : V) (ha : Q a ≠ 0) :
    dicksonValue Q (reflectionElement Q a ha) = 1 := by
  simpa only [mul_one, dicksonValue_one, zero_add] using
    dicksonValue_reflection_mul Q hQ a ha 1

include hQ in
/-- A generator has zero residual-rank parity, even when its parameter is singular. -/
theorem dicksonValue_siegel (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) :
    dicksonValue Q (siegelElement Q u v hu huv) = 0 := by
  by_cases hv : Q v = 0
  · exact dicksonParity_siegel_isotropic Q u v hu huv hQ hv
  · rw [siegelElement_reflection_factor Q u v hu huv hv,
      dicksonValue_reflection_mul Q hQ, dicksonValue_reflection Q hQ]
    decide

include hQ in
/-- The actual residual rank of a Siegel generator is zero or two. -/
theorem siegel_residual_finrank_zero_or_two (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) :
    Module.finrank F (residual Q (siegelIsometry Q u v hu huv)) = 0 ∨
      Module.finrank F (residual Q (siegelIsometry Q u v hu huv)) = 2 := by
  have hle := siegel_residual_finrank_le_two Q u v hu huv
  have hp := dicksonValue_siegel Q hQ u v hu huv
  change (Module.finrank F (residual Q (siegelIsometry Q u v hu huv)) : ZMod 2) = 0 at hp
  have hn : Module.finrank F (residual Q (siegelIsometry Q u v hu huv)) ≠ 1 := by
    intro h
    rw [h] at hp
    exact one_ne_zero hp
  omega
end Atlas.Orthogonal

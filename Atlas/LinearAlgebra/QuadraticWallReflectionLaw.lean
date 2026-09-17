import Atlas.LinearAlgebra.QuadraticResidualOutside
import Atlas.LinearAlgebra.QuadraticWallReflection

/-! # The general reflection law for Wall determinant classes -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
  (g : Q.IsometryEquiv Q) (a : V) (ha : Q a ≠ 0)

theorem reflectedIsometry_twice :
    reflectedIsometry Q (reflectedIsometry Q g a ha) a ha = g := by
  apply DFunLike.ext
  intro x
  exact Module.involutive_reflection (reflectionFunctional_self Q a ha) (g x)

/-- Multiplication by any anisotropic reflection multiplies the Wall class by Q(a). -/
theorem wallDeterminantClass_reflection :
    wallDeterminantClass Q hQ (reflectedIsometry Q g a ha) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) * wallDeterminantClass Q hQ g := by
  classical
  by_cases hmem : a ∈ residual Q g
  · have h := wallDeterminantClass_reflection_residual Q hQ g ⟨a, hmem⟩ ha
    have hs : Atlas.squareClass F (Units.mk0 (Q a) ha) *
        Atlas.squareClass F (Units.mk0 (Q a) ha) = 1 := by
      rw [← map_mul, ← pow_two, Atlas.squareClass_square]
    change wallDeterminantClass Q hQ g =
      Atlas.squareClass F (Units.mk0 (Q a) ha) *
        wallDeterminantClass Q hQ (reflectedIsometry Q g a ha) at h
    rw [h, ← mul_assoc, hs, one_mul]
  · have hmem' := outside_mem_reflected_residual Q g hQ a ha hmem
    have h := wallDeterminantClass_reflection_residual Q hQ
      (reflectedIsometry Q g a ha) ⟨a, hmem'⟩ ha
    change wallDeterminantClass Q hQ (reflectedIsometry Q g a ha) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) *
        wallDeterminantClass Q hQ
          (reflectedIsometry Q (reflectedIsometry Q g a ha) a ha) at h
    rw [reflectedIsometry_twice] at h
    exact h

end Atlas.Quadratic

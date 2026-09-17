import Atlas.LinearGroups.Orthogonal.EvenProjection
import Atlas.LinearAlgebra.QuadraticSquareRoot

/-! # Actual quadratic lifts of symplectic transformations in characteristic two -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

def evenDefect (g : Atlas.Symplectic.Sp n F) : QuadraticForm F (VectorD n F) :=
  formD n F - (formD n F).comp (Atlas.Symplectic.toLinear g).toLinearMap

theorem evenDefect_polar (g : Atlas.Symplectic.Sp n F) (x y : VectorD n F) :
    (evenDefect g).polarBilin x y = 0 := by
  have h := Atlas.Symplectic.preserves g x y
  rw [← polarD_eq_symplectic, ← polarD_eq_symplectic] at h
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar] at h
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, evenDefect,
    QuadraticMap.sub_apply, QuadraticMap.comp_apply, map_add]
  change (formD n F (x+y) - formD n F (g • x + g • y)) -
    (formD n F x - formD n F (g • x)) - (formD n F y - formD n F (g • y)) = 0
  linear_combination -h

def evenCorrection (g : Atlas.Symplectic.Sp n F) : VectorD n F →ₗ[F] F :=
  Atlas.Quadratic.squareRootLinear (evenDefect g) (evenDefect_polar g)

theorem evenCorrection_sq (g : Atlas.Symplectic.Sp n F) (x : VectorD n F) :
    evenCorrection g x ^ 2 = formD n F x - formD n F (g • x) :=
  Atlas.Quadratic.squareRootLinear_sq (evenDefect g) (evenDefect_polar g) x

def evenLiftLinear (g : Atlas.Symplectic.Sp n F) : VectorB n F ≃ₗ[F] VectorB n F where
  toFun x := (Atlas.Symplectic.toLinear g x.1, x.2 + evenCorrection g x.1)
  invFun x := ((Atlas.Symplectic.toLinear g).symm x.1,
    x.2 - evenCorrection g ((Atlas.Symplectic.toLinear g).symm x.1))
  left_inv x := by
    apply Prod.ext
    · exact (Atlas.Symplectic.toLinear g).symm_apply_apply x.1
    · change x.2 + evenCorrection g x.1 -
        evenCorrection g ((Atlas.Symplectic.toLinear g).symm (Atlas.Symplectic.toLinear g x.1)) = x.2
      rw [LinearEquiv.symm_apply_apply, add_sub_cancel_right]
  right_inv x := by
    apply Prod.ext
    · exact (Atlas.Symplectic.toLinear g).apply_symm_apply x.1
    · change x.2 - evenCorrection g ((Atlas.Symplectic.toLinear g).symm x.1) +
        evenCorrection g ((Atlas.Symplectic.toLinear g).symm x.1) = x.2
      rw [sub_add_cancel]
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · change x.2 + y.2 + evenCorrection g (x.1+y.1) =
        (x.2+evenCorrection g x.1)+(y.2+evenCorrection g y.1)
      rw [map_add]
      ring
  map_smul' a x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · change a*x.2+evenCorrection g (a • x.1) = a*(x.2+evenCorrection g x.1)
      rw [map_smul, smul_eq_mul]
      ring

theorem evenLift_preserves (g : Atlas.Symplectic.Sp n F) (x : VectorB n F) :
    formB n F (evenLiftLinear g x) = formB n F x := by
  rw [formB_apply]
  change formD n F (g • x.1) + (x.2+evenCorrection g x.1)^2 = formB n F x
  rw [formB_apply, add_sq, (show (2 : F) = 0 from CharTwo.two_eq_zero), zero_mul, zero_mul, add_zero, evenCorrection_sq]
  ring

def evenLift (g : Atlas.Symplectic.Sp n F) : O_B n F :=
  ⟨evenLiftLinear g, evenLift_preserves g⟩

end Atlas.Orthogonal

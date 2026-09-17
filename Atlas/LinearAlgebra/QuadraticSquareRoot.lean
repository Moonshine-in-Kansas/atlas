import Atlas.LinearAlgebra.QuadraticHyperbolic
import Mathlib.FieldTheory.Perfect

/-! # Quasilinear quadratic forms are squares of linear forms over perfect fields of characteristic two -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [CharP F 2] [PerfectRing F 2]
  [AddCommGroup V] [Module F V]

def squareRootLinear (Q : QuadraticForm F V) (hQ : ∀ x y, Q.polarBilin x y = 0) : V →ₗ[F] F where
  toFun x := (frobeniusEquiv F 2).symm (Q x)
  map_add' x y := by
    have h : Q (x+y) = Q x + Q y := by
      rw [QuadraticMap.map_add Q]
      change Q x + Q y + Q.polarBilin x y = Q x + Q y
      rw [hQ, add_zero]
    rw [h, map_add]
  map_smul' a x := by
    change (frobeniusEquiv F 2).symm (Q (a • x)) = a * (frobeniusEquiv F 2).symm (Q x)
    rw [Q.map_smul, smul_eq_mul, ← pow_two, map_mul]
    exact congrArg (· * (frobeniusEquiv F 2).symm (Q x))
      ((frobeniusEquiv F 2).symm_apply_apply a)

theorem squareRootLinear_sq (Q : QuadraticForm F V) (hQ : ∀ x y, Q.polarBilin x y = 0) (x : V) :
    squareRootLinear Q hQ x ^ 2 = Q x :=
  (frobeniusEquiv F 2).apply_symm_apply (Q x)

end Atlas.Quadratic

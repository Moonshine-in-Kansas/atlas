import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

/-! The rank-one odd quadratic matrix identity over arbitrary commutative rings.
The coordinate order is occupied, empty; the parity matrix is diag(-1,1).
These are local polynomial identities, not a global Clifford faithfulness theorem. -/
namespace Atlas.OddRankOneSpinMatrix
open scoped Matrix
variable {R : Type*} [CommRing R]

def gamma (x y z : R) : Matrix (Fin 2) (Fin 2) R := !![-z, x; y, z]
def upper (t : R) : Matrix (Fin 2) (Fin 2) R := !![1, t; 0, 1]
def lower (t : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; t, 1]

theorem gamma_injective : Function.Injective (fun v : R × R × R => gamma v.1 v.2.1 v.2.2) := by
  intro v w h
  have hx : v.1 = w.1 := by
    simpa [gamma] using congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 0 1) h
  have hy : v.2.1 = w.2.1 := by
    simpa [gamma] using congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) h
  have hz : v.2.2 = w.2.2 := by
    simpa [gamma] using congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 1) h
  exact Prod.ext hx (Prod.ext hy hz)

theorem gamma_sq (x y z : R) : gamma x y z * gamma x y z = (x*y+z^2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] <;> ring

theorem upper_mul_neg (t : R) : upper t * upper (-t) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.mul_apply, Fin.sum_univ_two]

theorem lower_mul_neg (t : R) : lower t * lower (-t) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, Matrix.mul_apply, Fin.sum_univ_two]

/-- The short raising root has Siegel parameter +t. -/
theorem upper_gamma (t x y z : R) :
    upper t * gamma x y z * upper (-t) = gamma (x+2*t*z-t^2*y) y (z-t*y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, gamma, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The opposite short root has Siegel parameter -t, with singular direction f. -/
theorem lower_gamma (t x y z : R) :
    lower t * gamma x y z * lower (-t) = gamma x (y-2*t*z-t^2*x) (z+t*x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, gamma, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem quadratic_upper (t x y z : R) :
    (x+2*t*z-t^2*y)*y+(z-t*y)^2 = x*y+z^2 := by ring

theorem quadratic_lower (t x y z : R) :
    x*(y-2*t*z-t^2*x)+(z+t*x)^2 = x*y+z^2 := by ring

/-- In characteristic two the odd polar radical is represented by scalar matrices;
the vector-coordinate map remains injective by gamma_injective. -/
theorem gamma_radical_charTwo (h2 : (2 : R) = 0) (z : R) : gamma 0 0 z = z • 1 := by
  have hz : z+z = 0 := by
    calc
      z+z = (2 : R)*z := by ring
      _ = 0 := by rw [h2, zero_mul]
  have hn : -z = z := by linear_combination -hz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.smul_apply, smul_eq_mul, hn]

end Atlas.OddRankOneSpinMatrix

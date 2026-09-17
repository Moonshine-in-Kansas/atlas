import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Wilson's integral split table, notes Eq. (4.11), in eight coordinates.
Lean index i represents Wilson x_(i+1). The product is named `mul`, and the
identity is named `unit`; the ambient function space's pointwise multiplication
is not the octonion multiplication. No associative algebra instance is asserted. -/
namespace Atlas.SplitOctonion
abbrev Carrier (F : Type*) := Fin 8 → F
variable {F : Type*} [CommRing F]

def basisVector (i : Fin 8) : Carrier F := Pi.single i 1

def mul (a b : Carrier F) : Carrier F :=
  ![a 0 * b 4 - a 1 * b 2 + a 2 * b 1 + a 3 * b 0,
    a 0 * b 5 + a 1 * b 3 + a 4 * b 1 - a 5 * b 0,
    - a 0 * b 6 + a 2 * b 3 + a 4 * b 2 + a 6 * b 0,
    - a 0 * b 7 + a 3 * b 3 - a 5 * b 2 - a 6 * b 1,
    - a 1 * b 6 - a 2 * b 5 + a 4 * b 4 - a 7 * b 0,
    a 1 * b 7 + a 3 * b 5 + a 5 * b 4 - a 7 * b 1,
    - a 2 * b 7 + a 3 * b 6 + a 6 * b 4 + a 7 * b 2,
    a 4 * b 7 + a 5 * b 6 - a 6 * b 5 + a 7 * b 3]

def unit : Carrier F := ![0,0,0,1,1,0,0,0]
def trace (a : Carrier F) : F := a 3 + a 4
def norm (a : Carrier F) : F := a 0*a 7+a 1*a 6+a 2*a 5+a 3*a 4
def conjugate (a : Carrier F) : Carrier F := trace a • unit - a

theorem unit_mul (a : Carrier F) : mul unit a = a := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul,unit]
theorem mul_unit (a : Carrier F) : mul a unit = a := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul,unit]

theorem mul_add (a b c : Carrier F) : mul a (b+c) = mul a b + mul a c := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul] <;> ring
theorem add_mul (a b c : Carrier F) : mul (a+b) c = mul a c + mul b c := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul] <;> ring
theorem mul_smul (r : F) (a b : Carrier F) : mul a (r • b) = r • mul a b := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul] <;> ring
theorem smul_mul (r : F) (a b : Carrier F) : mul (r • a) b = r • mul a b := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul] <;> ring

def multiplication : Carrier F →ₗ[F] Carrier F →ₗ[F] Carrier F where
  toFun a :=
    { toFun := mul a
      map_add' := mul_add a
      map_smul' := fun r b => mul_smul r a b }
  map_add' a b := by apply LinearMap.ext; intro c; exact add_mul a b c
  map_smul' r a := by apply LinearMap.ext; intro b; exact smul_mul r a b

/-- The quadratic relation, with no characteristic restriction. -/
theorem quadratic_identity (a : Carrier F) :
    mul a a - trace a • a + norm a • unit = 0 := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul,trace,norm,unit] <;> ring

theorem mul_conjugate (a : Carrier F) : mul a (conjugate a) = norm a • unit := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul,conjugate,trace,norm,unit] <;> ring

theorem conjugate_mul (a : Carrier F) : mul (conjugate a) a = norm a • unit := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul,conjugate,trace,norm,unit] <;> ring

theorem norm_mul (a b : Carrier F) : norm (mul a b) = norm a * norm b := by
  simp [Matrix.vecHead, Matrix.vecTail, mul,norm]; ring

theorem conjugate_mul_reverse (a b : Carrier F) :
    conjugate (mul a b) = mul (conjugate b) (conjugate a) := by
  ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, mul,conjugate,trace,unit] <;> ring
end Atlas.SplitOctonion

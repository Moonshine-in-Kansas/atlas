import Atlas.LinearGroups.F4.ShortWeyl
import Atlas.Algebra.SplitOctonion.NormComposition
import Mathlib.Tactic.Module

noncomputable section
namespace Atlas.F4
variable {R : Type*} [CommRing R]

theorem shortWeyl_conjugate_add (x y : Atlas.SplitOctonion.Carrier R) :
    Atlas.SplitOctonion.conjugate (x+y) =
      Atlas.SplitOctonion.conjugate x + Atlas.SplitOctonion.conjugate y := by
  funext i
  fin_cases i <;>
    simp [Matrix.vecHead, Matrix.vecTail, Atlas.SplitOctonion.conjugate, Atlas.SplitOctonion.trace, Atlas.SplitOctonion.unit] <;> ring

theorem shortWeyl_trace_smul (t : R) (x : Atlas.SplitOctonion.Carrier R) :
    Atlas.SplitOctonion.trace (t • x) = t * Atlas.SplitOctonion.trace x := by
  simp [Matrix.vecHead, Matrix.vecTail, Atlas.SplitOctonion.trace]; ring

def shortRootQuadraticApply (x : Atlas.SplitOctonion.Carrier R)
    (y : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  (0, ![0,0,-Atlas.SplitOctonion.mul x
    (Atlas.SplitOctonion.mul (Atlas.SplitOctonion.conjugate (y.2 2)) x)])

def shortRootQuadraticLinear (x : Atlas.SplitOctonion.Carrier R) :
    Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R where
  toFun := shortRootQuadraticApply x
  map_add' y z := by
    apply Prod.ext
    · simp [Matrix.vecHead, Matrix.vecTail, shortRootQuadraticApply]
    · funext i
      fin_cases i <;>
        simp [Matrix.vecHead, Matrix.vecTail, shortRootQuadraticApply, shortWeyl_conjugate_add,
          Atlas.SplitOctonion.add_mul, Atlas.SplitOctonion.mul_add] <;> abel
  map_smul' t y := by
    apply Prod.ext
    · simp [Matrix.vecHead, Matrix.vecTail, shortRootQuadraticApply]
    · funext i
      fin_cases i <;>
        simp [Matrix.vecHead, Matrix.vecTail, shortRootQuadraticApply, Atlas.SplitOctonion.conjugate_smul,
          Atlas.SplitOctonion.smul_mul, Atlas.SplitOctonion.mul_smul]

def shortRootFirstCoefficient (i : Fin 8) :
    Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R :=
  Atlas.Albert.shortRootLinear i 1 - LinearMap.id -
    shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector i)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The exact degree-two parameter formula. No interpolation or division is used. -/
theorem shortRoot_polynomial (i : Fin 8) (t : R) (y : Atlas.Albert.Carrier R) :
    Atlas.Albert.shortRootLinear i t y = y + t • shortRootFirstCoefficient i y +
      t^2 • shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector i) y := by
  apply Prod.ext
  · funext j
    fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, Atlas.Albert.shortRootLinear, Atlas.Albert.shortRootFormula,
        shortRootFirstCoefficient, shortRootQuadraticLinear, shortRootQuadraticApply,
        Atlas.SplitOctonion.conjugate_smul, Atlas.SplitOctonion.mul_smul,
        shortWeyl_trace_smul] <;> ring
  · funext j
    fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, Atlas.Albert.shortRootLinear, Atlas.Albert.shortRootFormula,
        shortRootFirstCoefficient, shortRootQuadraticLinear, shortRootQuadraticApply,
        Atlas.SplitOctonion.conjugate_smul, Atlas.SplitOctonion.mul_smul,
        Atlas.SplitOctonion.smul_mul, smul_smul] <;> module

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem shortRootQuadratic_map {S : Type*} [CommRing S] (φ : R →+* S)
    (x : Atlas.SplitOctonion.Carrier R) (y : Atlas.Albert.Carrier R) :
    shortRootQuadraticLinear (fun j => φ (x j)) (Atlas.Albert.map φ y) =
      Atlas.Albert.map φ (shortRootQuadraticLinear x y) := by
  apply Prod.ext
  · funext j; simp [Matrix.vecHead, Matrix.vecTail, shortRootQuadraticLinear, shortRootQuadraticApply, Atlas.Albert.map]
  · funext j k
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.vecHead, Matrix.vecTail, shortRootQuadraticLinear, shortRootQuadraticApply,
        Atlas.Albert.map, Atlas.SplitOctonion.mul, Atlas.SplitOctonion.conjugate,
        Atlas.SplitOctonion.trace, Atlas.SplitOctonion.unit]

theorem shortRootQuadratic_basis_map {S : Type*} [CommRing S] (φ : R →+* S)
    (i : Fin 8) (y : Atlas.Albert.Carrier R) :
    shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector i) (Atlas.Albert.map φ y) =
      Atlas.Albert.map φ (shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector i) y) := by
  have hp : (fun j => φ ((Atlas.SplitOctonion.basisVector i : Atlas.SplitOctonion.Carrier R) j)) =
      Atlas.SplitOctonion.basisVector i := by
    funext j
    by_cases h : j=i <;> simp [Matrix.vecHead, Matrix.vecTail, Atlas.SplitOctonion.basisVector, Pi.single_apply, h]
  rw [← hp]
  exact shortRootQuadratic_map φ _ y

theorem shortRootFirstCoefficient_map {S : Type*} [CommRing S] (φ : R →+* S)
    (i : Fin 8) (y : Atlas.Albert.Carrier R) :
    shortRootFirstCoefficient i (Atlas.Albert.map φ y) =
      Atlas.Albert.map φ (shortRootFirstCoefficient i y) := by
  change Atlas.Albert.shortRootLinear i 1 (Atlas.Albert.map φ y) - Atlas.Albert.map φ y -
      shortRootQuadraticLinear (Atlas.SplitOctonion.basisVector i) (Atlas.Albert.map φ y) = _
  rw [← map_one φ, Atlas.Albert.shortRootLinear_map, shortRootQuadratic_basis_map]
  apply Prod.ext
  · funext j; simp [Matrix.vecHead, Matrix.vecTail, Atlas.Albert.map, shortRootFirstCoefficient]
  · funext j k; simp [Matrix.vecHead, Matrix.vecTail, Atlas.Albert.map, shortRootFirstCoefficient]

end Atlas.F4

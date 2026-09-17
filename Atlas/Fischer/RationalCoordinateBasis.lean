import Atlas.Fischer.RationalCoordinateSpace
import Mathlib.LinearAlgebra.Pi

noncomputable section
namespace Atlas.Fischer

abbrev RationalCoordinateIndex := CoordinateIndex × Fin 2

def scalarRealThetaFunEquiv : Scalar ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  scalarRealThetaEquiv.trans (LinearEquiv.finTwoArrow ℚ ℚ).symm

/-- The actual rational coordinates of A, in the two scalar directions 1, theta. -/
def rationalCoordinateEquiv : Coordinates ≃ₗ[ℚ] (RationalCoordinateIndex → ℚ) where
  toFun x p := scalarRealThetaFunEquiv (x p.1) p.2
  invFun f i := scalarRealThetaFunEquiv.symm (fun j => f (i,j))
  left_inv x := by funext i; exact scalarRealThetaFunEquiv.symm_apply_apply (x i)
  right_inv f := by
    funext p
    exact congrFun (scalarRealThetaFunEquiv.apply_symm_apply (fun j => f (p.1,j))) p.2
  map_add' x y := by funext p; exact congrFun (map_add scalarRealThetaFunEquiv (x p.1) (y p.1)) p.2
  map_smul' a x := by funext p; exact congrFun (map_smul scalarRealThetaFunEquiv a (x p.1)) p.2

def rationalCoordinateBasis : Module.Basis RationalCoordinateIndex ℚ Coordinates :=
  Module.Basis.ofEquivFun rationalCoordinateEquiv

theorem rationalCoordinateEquiv_real (x : Coordinates) (i : CoordinateIndex) :
    rationalCoordinateEquiv x (i,0) = (x i).re - (x i).im / 2 := rfl

theorem rationalCoordinateEquiv_theta (x : Coordinates) (i : CoordinateIndex) :
    rationalCoordinateEquiv x (i,1) = (x i).im / 2 := rfl

/-- Every actual coordinate splits in the two rational scalar directions. -/
theorem rationalCoordinateEquiv_reconstruct (x : Coordinates) (i : CoordinateIndex) :
    x i = rationalCoordinateEquiv x (i,0) • (1 : Scalar) +
      rationalCoordinateEquiv x (i,1) • theta := scalarRealThetaEquiv_decomposition (x i)

end Atlas.Fischer

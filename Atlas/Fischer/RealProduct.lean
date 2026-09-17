import Atlas.Fischer.RealCoordinateSpace
import Atlas.Fischer.ProductMaps
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

noncomputable section
namespace Atlas.Fischer
open scoped TensorProduct

theorem product_rat_smul_left (a : ℚ) (x y : Coordinates) :
    product (a • x) y = a • product x y := by
  have h := product_smul_left (a : Scalar) x y
  simpa only [star_ratCast, Rat.cast_smul_eq_qsmul] using h

theorem product_rat_smul_right (a : ℚ) (x y : Coordinates) :
    product x (a • y) = a • product x y := by
  have h := product_smul_right (a : Scalar) x y
  simpa only [star_ratCast, Rat.cast_smul_eq_qsmul] using h

/-- The retained conjugate-bilinear E-product is bilinear over Q. -/
def rationalProduct : LinearMap.BilinMap ℚ Coordinates Coordinates where
  toFun x :=
    { toFun := product x
      map_add' := product_add_right x
      map_smul' := fun a y => product_rat_smul_right a x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact product_add_left x y z
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact product_rat_smul_left a x y

/-- Real scalar extension of the actual rational bilinear product. -/
def realProduct : LinearMap.BilinMap ℝ RealCoordinates RealCoordinates :=
  rationalProduct.baseChange ℝ

theorem realProduct_tmul (a b : ℝ) (x y : Coordinates) :
    realProduct (a ⊗ₜ[ℚ] x) (b ⊗ₜ[ℚ] y) = (a * b) ⊗ₜ[ℚ] product x y :=
  LinearMap.BilinMap.baseChange_tmul _ _ _ _ _

end Atlas.Fischer

import Atlas.Fischer.ProductMaps
import Mathlib.LinearAlgebra.Trace

noncomputable section
namespace Atlas.Fischer

/-- The composition L_x L_y is linear although each factor is conjugate-linear. -/
def productLeftComposite (x y : Coordinates) : Coordinates →ₗ[Scalar] Coordinates where
  toFun z := product (product z y) x
  map_add' z w := by rw [product_add_left,product_add_left]
  map_smul' a z := by
    simp only [product_smul_left,star_star,RingHom.id_apply]

theorem productLeftComposite_apply (x y z : Coordinates) :
    productLeftComposite x y z = product (product z y) x := rfl

/-- The intrinsic E-linear trace of the actual two multiplication maps. -/
def productTrace (x y : Coordinates) : Scalar :=
  LinearMap.trace Scalar Coordinates (productLeftComposite x y)

theorem coordinateLinearMap_trace (f : Coordinates →ₗ[Scalar] Coordinates) :
    LinearMap.trace Scalar Coordinates f = ∑ i, f (coordinateVector i) i := by
  classical
  rw [LinearMap.trace_eq_matrix_trace Scalar (Pi.basisFun Scalar CoordinateIndex)]
  simp [Matrix.trace,LinearMap.toMatrix_apply,Pi.basisFun_apply,coordinateVector]

theorem productTrace_smul_left (a : Scalar) (x y : Coordinates) :
    productTrace (a • x) y = star a * productTrace x y := by
  have h : productLeftComposite (a • x) y = star a • productLeftComposite x y := by
    apply LinearMap.ext
    intro z
    simp [productLeftComposite,product_smul_right]
  unfold productTrace
  rw [h,map_smul,smul_eq_mul]

theorem productTrace_smul_right (a : Scalar) (x y : Coordinates) :
    productTrace x (a • y) = a * productTrace x y := by
  have h : productLeftComposite x (a • y) = a • productLeftComposite x y := by
    apply LinearMap.ext
    intro z
    simp [productLeftComposite,product_smul_right,product_smul_left]
  unfold productTrace
  rw [h,map_smul,smul_eq_mul]

end Atlas.Fischer

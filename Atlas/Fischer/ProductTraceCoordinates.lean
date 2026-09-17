import Atlas.Fischer.ProductTraceMaps
import Atlas.Fischer.WeightedCubicTensor
import Atlas.Fischer.ParkerMultiplicativity

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

theorem product_coordinateVector_right (x : Coordinates) (i : CoordinateIndex) :
    product x (coordinateVector i) = ∑ j, star (x j) • basisProduct j i := by
  conv_lhs => rw [← coordinates_sum_basis x]
  rw [product_sum_left]
  simp only [product_smul_left, product_coordinateVector]

/-- The intrinsic trace and weighted cubic contraction agree with the precise
linear-first Hermitian ordering. No numerical slice identity is assumed. -/
theorem productTrace_coordinateVector (i j : CoordinateIndex) :
    productTrace (coordinateVector i) (coordinateVector j) = coordinateCubicSlice j i := by
  rw [productTrace, coordinateLinearMap_trace]
  change (∑ a, product (product (coordinateVector a) (coordinateVector j))
    (coordinateVector i) a) = _
  simp_rw [product_coordinateVector, product_coordinateVector_right]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinateCubicSlice]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [basisProduct_from_coordinateCubic b a j, basisProduct_from_coordinateCubic a b i]
  simp only [star_mul, star_star, inverseCoordinateMetric_star]
  have hj : coordinateCubic b a j = coordinateCubic j a b := by
    rw [coordinateCubic_swap_last b a j, coordinateCubic_swap_first b j a,
      coordinateCubic_swap_last j b a]
  have hi : coordinateCubic a b i = coordinateCubic i a b := by
    rw [coordinateCubic_swap_last a b i, coordinateCubic_swap_first a i b]
  rw [hj, hi]
  ring

theorem productTrace_add_first (x y z : Coordinates) :
    productTrace (x + y) z = productTrace x z + productTrace y z := by
  have h : productLeftComposite (x + y) z = productLeftComposite x z + productLeftComposite y z := by
    apply LinearMap.ext
    intro a
    exact product_add_right _ _ _
  rw [productTrace, h, map_add]
  rfl

theorem productTrace_add_second (x y z : Coordinates) :
    productTrace x (y + z) = productTrace x y + productTrace x z := by
  have h : productLeftComposite x (y + z) = productLeftComposite x y + productLeftComposite x z := by
    apply LinearMap.ext
    intro a
    change product (product a (y + z)) x = _
    rw [product_add_right, product_add_left]
    rfl
  rw [productTrace, h, map_add]
  rfl

theorem productTrace_smul_first (a : Scalar) (x y : Coordinates) :
    productTrace (a • x) y = star a * productTrace x y := productTrace_smul_left a x y

theorem productTrace_smul_second (a : Scalar) (x y : Coordinates) :
    productTrace x (a • y) = a * productTrace x y := productTrace_smul_right a x y

def productTraceFirstMap (y : Coordinates) : Coordinates →ₛₗ[starRingEnd Scalar] Scalar where
  toFun x := productTrace x y
  map_add' x z := productTrace_add_first x z y
  map_smul' a x := productTrace_smul_left a x y

def productTraceSecondMap (x : Coordinates) : Coordinates →ₗ[Scalar] Scalar where
  toFun y := productTrace x y
  map_add' y z := productTrace_add_second x y z
  map_smul' a y := productTrace_smul_right a x y

/-- The complete weighted-coordinate expansion of the intrinsic trace. -/
theorem productTrace_coordinate_expansion (x y : Coordinates) :
    productTrace x y = ∑ i, ∑ j, star (x i) * y j * coordinateCubicSlice j i := by
  have hfirst : productTrace x y =
      ∑ i, star (x i) * productTrace (coordinateVector i) y := by
    conv_lhs => rw [← coordinates_sum_basis x]
    change productTraceFirstMap y _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact productTrace_smul_left (x i) (coordinateVector i) y
  have hsecond (i : CoordinateIndex) : productTrace (coordinateVector i) y =
      ∑ j, y j * coordinateCubicSlice j i := by
    conv_lhs => rw [← coordinates_sum_basis y]
    change productTraceSecondMap (coordinateVector i) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change productTrace (coordinateVector i) (y j • coordinateVector j) = _
    rw [productTrace_smul_right, productTrace_coordinateVector]
  rw [hfirst]
  simp_rw [hsecond, Finset.mul_sum, mul_assoc]

end Atlas.Fischer

import Atlas.Fischer.ProductCommutativity

namespace Atlas.Fischer

noncomputable def productLeftMap (y : Coordinates) :
    Coordinates →ₛₗ[starRingEnd Scalar] Coordinates where
  toFun x := product x y
  map_add' x x' := product_add_left x x' y
  map_smul' a x := product_smul_left a x y

noncomputable def productRightMap (x : Coordinates) :
    Coordinates →ₛₗ[starRingEnd Scalar] Coordinates where
  toFun y := product x y
  map_add' y y' := product_add_right x y y'
  map_smul' a y := product_smul_right a x y

theorem product_sum_left {ι : Type*} (s : Finset ι) (f : ι → Coordinates) (y : Coordinates) :
    product (∑ i ∈ s, f i) y = ∑ i ∈ s, product (f i) y :=
  map_sum (productLeftMap y) _ _

theorem product_sum_right {ι : Type*} (s : Finset ι) (f : ι → Coordinates) (x : Coordinates) :
    product x (∑ i ∈ s, f i) = ∑ i ∈ s, product x (f i) :=
  map_sum (productRightMap x) _ _

theorem product_sub_left (x y z : Coordinates) :
    product (x - y) z = product x z - product y z := map_sub (productLeftMap z) x y

theorem product_sub_right (x y z : Coordinates) :
    product x (y - z) = product x y - product x z := map_sub (productRightMap x) y z

end Atlas.Fischer

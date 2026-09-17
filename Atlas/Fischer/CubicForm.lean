import Atlas.Fischer.ProductCommutativity

namespace Atlas.Fischer

/-- The cubic tensor is initially defined over the exact coefficient field E. -/
noncomputable def cubic (x y z : Coordinates) : Scalar := hermitian x (product y z)

theorem hermitian_add_right (x y z : Coordinates) :
    hermitian x (y + z) = hermitian x y + hermitian x z := by
  rw [← star_star (hermitian x (y + z)), hermitian_star, hermitian_add_left,
    star_add, hermitian_star, hermitian_star]

theorem cubic_add_first (x x' y z : Coordinates) :
    cubic (x + x') y z = cubic x y z + cubic x' y z := hermitian_add_left _ _ _

theorem cubic_add_second (x y y' z : Coordinates) :
    cubic x (y + y') z = cubic x y z + cubic x y' z := by
  rw [cubic, product_add_left, hermitian_add_right]
  rfl

theorem cubic_add_third (x y z z' : Coordinates) :
    cubic x y (z + z') = cubic x y z + cubic x y z' := by
  rw [cubic, product_add_right, hermitian_add_right]
  rfl

theorem cubic_smul_first (a : Scalar) (x y z : Coordinates) :
    cubic (a • x) y z = a * cubic x y z := hermitian_smul_left _ _ _

theorem cubic_smul_second (a : Scalar) (x y z : Coordinates) :
    cubic x (a • y) z = a * cubic x y z := by
  rw [cubic, product_smul_left, hermitian_smul_right, star_star]
  rfl

theorem cubic_smul_third (a : Scalar) (x y z : Coordinates) :
    cubic x y (a • z) = a * cubic x y z := by
  rw [cubic, product_smul_right, hermitian_smul_right, star_star]
  rfl

theorem cubic_swap_last (x y z : Coordinates) : cubic x y z = cubic x z y := by
  rw [cubic, product_comm]
  rfl

end Atlas.Fischer

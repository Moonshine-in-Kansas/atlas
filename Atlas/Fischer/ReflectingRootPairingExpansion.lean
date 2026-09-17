import Atlas.Fischer.ReflectingRoots
import Atlas.Fischer.RootProductSquare
import Atlas.Fischer.RootPhases

noncomputable section
namespace Atlas.Fischer

/-- The first quadratic product identity forced by antiunitarity and the root equations. -/
theorem reflectingRoot_product_twice (r s : Coordinates) (hr : IsReflectingRoot r) :
    product (product r s) r = s + (11 * star (hermitian r s)) • r := by
  have h := congrArg (fun f : Module.End Scalar Coordinates => f s)
    (rootProduct_square r hr.1.1 hr.1.2 hr.2.1)
  simpa only [productLeftComposite_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, rootRankOne_apply, hermitian_star, smul_smul,
    product_comm s r] using h

/-- Expanding the square of the image of a reflecting root gives the first exact
expression for the square of their product; no ray membership is assumed. -/
theorem reflectingRoot_product_square_expansion (r s : Coordinates)
    (hr : IsReflectingRoot r) (hs : IsRoot s) :
    product (product r s) (product r s) =
      (10 : Scalar) • product r s + (2 * star (hermitian r s)) • s +
        (12 * star (hermitian r s)^2 - 10 * hermitian r s) • r := by
  have h := hr.2.2.2 s s
  rw [hs.2, rootMap_smul] at h
  norm_num at h
  simp only [rootMap, product_sub_left, product_sub_right, product_smul_left,
    product_smul_right, hr.1.2, smul_smul, product_comm s r] at h
  rw [product_comm r (product r s), reflectingRoot_product_twice r s hr] at h
  linear_combination (norm := module) -h

/-- The two reflected root-square expansions impose a scalar polynomial relation. -/
theorem reflectingRoot_pairing_polynomial (r s : Coordinates)
    (hr : IsReflectingRoot r) (hs : IsReflectingRoot s) :
    (star (hermitian r s)^2 - hermitian r s) • r +
      (star (hermitian r s) - hermitian r s^2) • s = 0 := by
  have h1 := reflectingRoot_product_square_expansion r s hr hs.1
  have h2 := reflectingRoot_product_square_expansion s r hs hr.1
  rw [product_comm s r, ← hermitian_star r s, star_star] at h2
  linear_combination (norm := module) (1 / 12 : Scalar) • h2 - (1 / 12 : Scalar) • h1

end Atlas.Fischer

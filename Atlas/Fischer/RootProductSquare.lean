import Atlas.Algebra.RankOneTrace
import Atlas.Fischer.ProductTraceMaps
import Atlas.Fischer.RootMapSymmetry
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace Atlas.Fischer

/-- The first-slot linear functional of the retained Hermitian form. -/
def rootHermitianFunctional (r : Coordinates) : Coordinates →ₗ[Scalar] Scalar where
  toFun x := hermitian x r
  map_add' x y := hermitian_add_left x y r
  map_smul' a x := hermitian_smul_left a x r

/-- The actual linear rank-one operator x ↦ h(x,r)r. -/
def rootRankOne (r : Coordinates) : Module.End Scalar Coordinates :=
  (rootHermitianFunctional r).smulRight r

theorem rootRankOne_apply (r x : Coordinates) : rootRankOne r x = hermitian x r • r := rfl

theorem rootRankOne_square (r : Coordinates) (hn : hermitian r r = 9) :
    rootRankOne r ^ 2 = (9 : Scalar) • rootRankOne r := by
  rw [rootRankOne, Atlas.Algebra.rankOne_smulRight_square]
  change hermitian r r • _ = _
  rw [hn]

theorem rootRankOne_trace (r : Coordinates) :
    LinearMap.trace Scalar Coordinates (rootRankOne r) = hermitian r r :=
  LinearMap.trace_smulRight _ _

/-- Cubic symmetry evaluates the mixed rank-one term using the root equation. -/
theorem rootProduct_pairing (r x : Coordinates) (he : product r r = (10 : Scalar) • r) :
    hermitian r (product x r) = (10 : Scalar) * hermitian x r := by
  change cubic r x r = _
  rw [cubic_swap_first]
  change hermitian x (product r r) = _
  rw [he, hermitian_smul_right]
  norm_num

/-- The source R conjugate(R) identity in the actual weighted coordinate space.
Only the two root equations and antiunitarity are assumed, not multiplicativity. -/
theorem rootProduct_square (r : Coordinates) (hn : hermitian r r = 9)
    (he : product r r = (10 : Scalar) • r) (ha : RootMapAntiunitary r) :
    productLeftComposite r r = 1 + (11 : Scalar) • rootRankOne r := by
  apply LinearMap.ext
  intro x
  have hi := rootMap_involutive_of_antiunitary r ha x
  have hp := rootProduct_pairing r x he
  simp only [rootMap, product_sub_left, product_smul_left, he, hermitian_sub_right,
    hermitian_smul_right, hermitian_star, hp, hn, smul_smul] at hi
  change product (product x r) r = x + (11 : Scalar) • (hermitian x r • r)
  linear_combination (norm := module) hi

/-- The one-rank-one tensor term has the exact required trace, without choosing
an eigenspace decomposition or adjoining square roots of metric weights. -/
theorem rootProduct_square_trace_square (r : Coordinates) (hn : hermitian r r = 9)
    (he : product r r = (10 : Scalar) • r) (ha : RootMapAntiunitary r) :
    LinearMap.trace Scalar Coordinates ((productLeftComposite r r) ^ 2) = 10782 := by
  rw [rootProduct_square r hn he ha]
  exact Atlas.Algebra.trace_one_add_eleven_rankOne_square
    (rootHermitianFunctional r) r hn coordinates_dimension

end Atlas.Fischer

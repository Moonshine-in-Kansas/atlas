import Atlas.Fischer.ReflectingRayFamily
import Atlas.Fischer.ReflectingRootAutomaticMoments

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

instance reflectingRootParameter_fintype : Fintype ReflectingRootParameter := Fintype.ofFinite _

theorem reflectingRootParameter_fintype_card : Fintype.card ReflectingRootParameter = 306936 := by
  rw [← Nat.card_eq_fintype_card]
  exact reflectingRootParameter_card

theorem reflectingRootParameter_distinct_phases (i j : ReflectingRootParameter) (hij : i ≠ j) :
    ¬ ∃ a : Mu3, reflectingRootParameterVector j =
      (a.val.val : Scalar) • reflectingRootParameterVector i := by
  intro h
  exact hij (reflectingRootParameterRay_injective
    ((rootRay_eq_iff_mu3 _ _).mpr h).symm)

theorem reflectingFamily_frame (x : Coordinates) :
    reflectingFrameOperator reflectingRootParameterVector x = (3528 : Scalar) • x :=
  reflectingFrameOperator_eq_3528 _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card x

theorem reflectingFamily_momentProduct (x y : Coordinates) :
    reflectingMomentProduct reflectingRootParameterVector x y = (360 : Scalar) • product x y :=
  reflectingMomentProduct_eq_360 _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card x y

theorem reflectingFamily_second_moment (x y : Coordinates) :
    (∑ j : ReflectingRootParameter, hermitian x (reflectingRootParameterVector j) *
      hermitian (reflectingRootParameterVector j) y) = 3528 * hermitian x y :=
  reflectingRoot_second_moment _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card x y

theorem reflectingFamily_third_moment (x y z : Coordinates) :
    (∑ j : ReflectingRootParameter, hermitian x (reflectingRootParameterVector j) *
      hermitian y (reflectingRootParameterVector j) * hermitian z (reflectingRootParameterVector j)) =
      360 * cubic x y z :=
  reflectingRoot_third_moment _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card x y z

theorem reflectingFamily_span :
    Submodule.span Scalar (Set.range reflectingRootParameterVector) = ⊤ :=
  reflectingRoot_span_top _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card

theorem reflectingFamily_product_reconstruction (x y : Coordinates) :
    product x y = (1 / 360 : Scalar) • (∑ j : ReflectingRootParameter,
      (hermitian (reflectingRootParameterVector j) x * hermitian (reflectingRootParameterVector j) y) •
        reflectingRootParameterVector j) :=
  reflectingRoot_product_reconstruction _ reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card x y

/-- Genuine E-basis, not a combinatorial unordered-pair replacement. -/
def reflectingFamilySquareBasis : Module.Basis ReflectingRootParameter Scalar
    (Atlas.Algebra.symmetricMatrixSpace Scalar CoordinateIndex) :=
  reflectingRootSquareBasis reflectingRootParameterVector reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card

end Atlas.Fischer

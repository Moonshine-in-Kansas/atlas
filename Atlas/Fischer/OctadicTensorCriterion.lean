import Atlas.Fischer.RootTensorCriterion
import Atlas.Fischer.OctadicReflections

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem rootMapAntiunitary_phase (r : Coordinates) (h : RootMapAntiunitary r)
    (a : Scalar) (ha : a ^ 3 = 1) : RootMapAntiunitary (a • r) := by
  intro x y
  rw [rootMap_phase r x a ha, rootMap_phase r y a ha,
    hermitian_smul_left, hermitian_smul_right, h, star_pow]
  have hn := cube_root_unit_norm ha
  calc
    _ = (star a * a) ^ 2 * star (hermitian x y) := by ring
    _ = _ := by rw [hn]; norm_num

/-- Conditional application to every actual calibrated octadic character root. -/
theorem octadicReflection_product_of_quintic
    (hK : ∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) (x y : Coordinates) :
    octadicReflection Q χ (product x y) = product (octadicReflection Q χ x) (octadicReflection Q χ y) := by
  exact rootMap_product_of_quintic hK _ (octadicRoot_isRoot Q χ).1
    (octadicRoot_isRoot Q χ).2 (octadicRoot_antiunitary Q χ) x y

/-- Every cube-root-of-unity phase is covered, with the universal contraction
identity still explicit rather than silently assuming octadic multiplicativity. -/
theorem octadicRoot_phase_product_of_quintic
    (hK : ∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O)
    (a : Scalar) (ha : a ^ 3 = 1) (x y : Coordinates) :
    rootMap (a • octadicRoot Q χ) (product x y) =
      product (rootMap (a • octadicRoot Q χ) x) (rootMap (a • octadicRoot Q χ) y) := by
  have hr := root_phase (octadicRoot Q χ) (octadicRoot_isRoot Q χ) a ha
  exact rootMap_product_of_quintic hK _ hr.1 hr.2
    (rootMapAntiunitary_phase _ (octadicRoot_antiunitary Q χ) a ha) x y

theorem octadicRoot_phase_package_of_quintic
    (hK : ∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O)
    (a : Scalar) (ha : a ^ 3 = 1) :
    IsRoot (a • octadicRoot Q χ) ∧ RootMapAntiunitary (a • octadicRoot Q χ) ∧
    Function.Involutive (rootMap (a • octadicRoot Q χ)) ∧
      ∀ x y, rootMap (a • octadicRoot Q χ) (product x y) =
        product (rootMap (a • octadicRoot Q χ) x) (rootMap (a • octadicRoot Q χ) y) := by
  have hr := root_phase (octadicRoot Q χ) (octadicRoot_isRoot Q χ) a ha
  have hh := rootMapAntiunitary_phase _ (octadicRoot_antiunitary Q χ) a ha
  exact ⟨hr, hh, rootMap_involutive_of_antiunitary _ hh,
    octadicRoot_phase_product_of_quintic hK Q χ a ha⟩

end Atlas.Fischer

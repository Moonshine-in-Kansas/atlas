import Atlas.Fischer.RootTensorTheorem
import Atlas.Fischer.OctadicTensorCriterion

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadicReflection_product {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (x y : Coordinates) :
    octadicReflection Q χ (product x y)=product (octadicReflection Q χ x) (octadicReflection Q χ y) :=
  octadicReflection_product_of_quintic coordinateQuintic_eq_1002_coordinateCubic Q χ x y

theorem octadicRoot_phase_product {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (a : Scalar) (ha : a^3=1) (x y : Coordinates) :
    rootMap (a • octadicRoot Q χ) (product x y)=
      product (rootMap (a • octadicRoot Q χ) x) (rootMap (a • octadicRoot Q χ) y) :=
  octadicRoot_phase_product_of_quintic coordinateQuintic_eq_1002_coordinateCubic Q χ a ha x y

/-- Every actual calibrated octadic character root and every cubic scalar phase
has its root equations, antiunitarity, involutivity and multiplicativity proved. -/
theorem octadicRoot_phase_algebra_package {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (a : Scalar) (ha : a^3=1) :
    IsRoot (a • octadicRoot Q χ) ∧ RootMapAntiunitary (a • octadicRoot Q χ) ∧
      Function.Involutive (rootMap (a • octadicRoot Q χ)) ∧
      ∀ x y, rootMap (a • octadicRoot Q χ) (product x y)=
        product (rootMap (a • octadicRoot Q χ) x) (rootMap (a • octadicRoot Q χ) y) :=
  octadicRoot_phase_package_of_quintic coordinateQuintic_eq_1002_coordinateCubic Q χ a ha

/-- Actual octadic phases give untagged conjugate-linear algebra automorphisms. -/
def octadicPhaseAlgebraAutomorphism {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (a : Scalar) (ha : a^3=1) : SemilinearAlgebraAutomorphism :=
  rootAlgebraAutomorphism (a • octadicRoot Q χ)
    (root_phase _ (octadicRoot_isRoot Q χ) a ha).1
    (root_phase _ (octadicRoot_isRoot Q χ) a ha).2
    (rootMapAntiunitary_phase _ (octadicRoot_antiunitary Q χ) a ha)

theorem octadicPhaseAlgebraAutomorphism_apply {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (a : Scalar) (ha : a^3=1) (x : Coordinates) :
    (octadicPhaseAlgebraAutomorphism Q χ a ha).val x=rootMap (a • octadicRoot Q χ) x := rfl

theorem octadicPhaseAlgebraAutomorphism_parity {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (a : Scalar) (ha : a^3=1) :
    semilinearAlgebraParity (octadicPhaseAlgebraAutomorphism Q χ a ha)=1 :=
  rootAlgebraAutomorphism_parity _ _ _ _

theorem octadicPhaseAlgebraAutomorphism_square {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (a : Scalar) (ha : a^3=1) :
    (octadicPhaseAlgebraAutomorphism Q χ a ha)^2=1 :=
  rootAlgebraAutomorphism_square _ _ _ _

theorem octadicPhaseAlgebraAutomorphism_not_linear {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (a : Scalar) (ha : a^3=1) :
    octadicPhaseAlgebraAutomorphism Q χ a ha ∉ linearAlgebraAutomorphisms :=
  rootAlgebraAutomorphism_not_linear _ _ _ _

end Atlas.Fischer

import Atlas.Fischer.RootTensorCriterion
import Atlas.Fischer.QuinticTensorIdentity
import Atlas.Fischer.RootMapEquivalence
import Atlas.Fischer.SemilinearAlgebraAutomorphisms

noncomputable section
namespace Atlas.Fischer

/-- The actual cubic defect vanishes under precisely the root equations and
antiunitarity; the universal tensor contraction is now a theorem. -/
theorem rootCubicDefectNorm_zero (r : Coordinates)
    (hn : hermitian r r=9) (he : product r r=(10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : rootCubicDefectNorm r=0 :=
  rootCubicDefectNorm_zero_of_quintic coordinateQuintic_eq_1002_coordinateCubic r hn he ha

theorem rootMap_product (r : Coordinates)
    (hn : hermitian r r=9) (he : product r r=(10 : Scalar) • r)
    (ha : RootMapAntiunitary r) (x y : Coordinates) :
    rootMap r (product x y)=product (rootMap r x) (rootMap r y) :=
  rootMap_product_of_quintic coordinateQuintic_eq_1002_coordinateCubic r hn he ha x y

/-- Unconditional tensor criterion for the retained algebra. Only the root
norm, square equation and antiunitarity are hypotheses. -/
theorem rootMap_algebra_criterion (r : Coordinates)
    (hn : hermitian r r=9) (he : product r r=(10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : Function.Involutive (rootMap r) ∧
      ∀ x y, rootMap r (product x y)=product (rootMap r x) (rootMap r y) :=
  rootMap_tensor_criterion coordinateQuintic_eq_1002_coordinateCubic r hn he ha

/-- The actual conjugate-linear root permutation, inside the existing untagged
semilinear automorphism group of the nonassociative algebra. -/
def rootAlgebraAutomorphism (r : Coordinates)
    (hn : hermitian r r=9) (he : product r r=(10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : SemilinearAlgebraAutomorphism :=
  ⟨(rootMapEquivalence r ha).toEquiv,rootMap_add r,
    rootMap_product r hn he ha,1,fun a x => by
      change rootMap r (a • x)=scalarParityAut 1 a • rootMap r x
      simpa only [scalarParityAut_one] using rootMap_smul r x a⟩

theorem rootAlgebraAutomorphism_apply (r : Coordinates)
    (hn : hermitian r r=9) (he : product r r=(10 : Scalar) • r)
    (ha : RootMapAntiunitary r) (x : Coordinates) :
    (rootAlgebraAutomorphism r hn he ha).val x=rootMap r x := rfl

theorem rootAlgebraAutomorphism_parity (r : Coordinates)
    (hn : hermitian r r=9) (he : product r r=(10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : semilinearAlgebraParity (rootAlgebraAutomorphism r hn he ha)=1 := by
  apply semilinearAlgebraParity_unique
  intro a x
  simpa only [rootAlgebraAutomorphism_apply,scalarParityAut_one] using rootMap_smul r x a

theorem rootAlgebraAutomorphism_square (r : Coordinates)
    (hn : hermitian r r=9) (he : product r r=(10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : (rootAlgebraAutomorphism r hn he ha)^2=1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (rootAlgebraAutomorphism r hn he ha).val
    ((rootAlgebraAutomorphism r hn he ha).val x)=x
  exact rootMap_involutive_of_antiunitary r ha x

theorem rootAlgebraAutomorphism_not_linear (r : Coordinates)
    (hn : hermitian r r=9) (he : product r r=(10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : rootAlgebraAutomorphism r hn he ha ∉ linearAlgebraAutomorphisms := by
  intro h
  have hz : semilinearAlgebraParity (rootAlgebraAutomorphism r hn he ha)=0 := h
  rw [rootAlgebraAutomorphism_parity] at hz
  exact one_ne_zero hz

end Atlas.Fischer

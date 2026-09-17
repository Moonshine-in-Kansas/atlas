import Atlas.Fischer.CubicTensorDefectExpansion
import Atlas.Fischer.IntrinsicTraceForm

noncomputable section
namespace Atlas.Fischer

/-- The universal quintic identity closes the actual root's cubic defect norm.
The contraction identity is an explicit obligation until Job23 T2 proves it. -/
theorem rootCubicDefectNorm_zero_of_quintic
    (hK : ∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    (r : Coordinates) (hn : hermitian r r = 9) (he : product r r = (10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : rootCubicDefectNorm r = 0 := by
  rw [rootCubicDefectNorm_antiunitary r ha, coordinateCubicNorm_eq,
    cubicOperatorContraction_rootMap_eq hK r hn he ha]
  norm_num

/-- Source root-tensor criterion in the actual algebra, with the universal
quintic coefficient theorem retained as its precise outstanding hypothesis. -/
theorem rootMap_product_of_quintic
    (hK : ∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    (r : Coordinates) (hn : hermitian r r = 9) (he : product r r = (10 : Scalar) • r)
    (ha : RootMapAntiunitary r) (x y : Coordinates) :
    rootMap r (product x y) = product (rootMap r x) (rootMap r y) :=
  rootMap_product_of_defectNorm_zero r ha (rootCubicDefectNorm_zero_of_quintic hK r hn he ha) x y

/-- Conditional involutory-automorphism conclusion; no multiplicativity is used
in the tensor or norm arguments supplying this implication. -/
theorem rootMap_tensor_criterion
    (hK : ∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r)
    (r : Coordinates) (hn : hermitian r r = 9) (he : product r r = (10 : Scalar) • r)
    (ha : RootMapAntiunitary r) : Function.Involutive (rootMap r) ∧
      ∀ x y, rootMap r (product x y) = product (rootMap r x) (rootMap r y) :=
  ⟨rootMap_involutive_of_antiunitary r ha, rootMap_product_of_quintic hK r hn he ha⟩

end Atlas.Fischer

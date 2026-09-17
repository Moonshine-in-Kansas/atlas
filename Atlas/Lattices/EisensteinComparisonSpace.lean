import Atlas.Lattices.EisensteinComparisonMatrix

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra Matrix

/-- The explicit rational comparison; lattice equality is a separate obligation. -/
noncomputable def eisensteinComparison : EisensteinRationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  eisensteinRealCoordinates.trans
    (Matrix.toLin'OfInv eisensteinComparison_inverse_matrix eisensteinComparison_matrix_inverse)

@[simp] theorem eisensteinComparison_apply (z : EisensteinRationalCoordinates) :
    eisensteinComparison z = eisensteinComparisonMatrix *ᵥ eisensteinRealCoordinates z := rfl

@[simp] theorem eisensteinComparison_symm_apply (x : RationalCoordinates) :
    eisensteinComparison.symm x =
      eisensteinRealCoordinates.symm (eisensteinComparisonInverseMatrix *ᵥ x) := rfl

theorem eisensteinBilinear_eq_gram (z w : EisensteinRationalCoordinates) :
    eisensteinBilinear z w = dotProduct (eisensteinRealCoordinates z)
      (eisensteinRealGram *ᵥ eisensteinRealCoordinates w) := by
  unfold eisensteinBilinear eisensteinHermitian
  rw [eisensteinReal_smul, eisensteinReal_sum]
  simp [dotProduct, Matrix.mulVec, eisensteinRealGram, eisensteinRealCoordinates,
    Fintype.sum_prod_type, Fin.sum_univ_two, eisensteinReal, Finset.mul_sum,
    mul_ite, Finset.sum_add_distrib, Finset.sum_mul]
  simp only [add_mul, sub_mul, mul_add, mul_sub, neg_mul, mul_neg,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring_nf
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem eisensteinComparison_isometry (z w : EisensteinRationalCoordinates) :
    rationalForm (eisensteinComparison z) (eisensteinComparison w) =
      eisensteinBilinear z w := by
  rw [eisensteinBilinear_eq_gram]
  change (1/8 : ℚ) * dotProduct
    (eisensteinComparisonMatrix *ᵥ eisensteinRealCoordinates z)
    (eisensteinComparisonMatrix *ᵥ eisensteinRealCoordinates w) = _
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    eisensteinComparison_matrix_gram]
  simp [Matrix.smul_mulVec, dotProduct_smul]

end Atlas.Lattices

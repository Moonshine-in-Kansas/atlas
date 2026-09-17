import Atlas.Lattices.IcosianComparisonMatrix

namespace Atlas.Lattices
open scoped Matrix

/-- Actual rational coordinate isometry. Integral lattice equality is proved separately. -/
noncomputable def icosianComparison : IcosianRationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  icosianRealCoordinates.trans
    (Matrix.toLin'OfInv icosianComparison_inverse_matrix icosianComparison_matrix_inverse)

@[simp] theorem icosianComparison_apply (z : IcosianRationalCoordinates) :
    icosianComparison z = icosianComparisonMatrix *ᵥ icosianRealCoordinates z := rfl

@[simp] theorem icosianComparison_symm_apply (x : RationalCoordinates) :
    icosianComparison.symm x =
      icosianRealCoordinates.symm (icosianComparisonInverseMatrix *ᵥ x) := rfl

theorem icosianComparison_isometry (z w : IcosianRationalCoordinates) :
    rationalForm (icosianComparison z) (icosianComparison w) = icosianBilinear z w := by
  rw [icosianBilinear_eq_dot]
  change (1/8 : ℚ) * dotProduct
    (icosianComparisonMatrix *ᵥ icosianRealCoordinates z)
    (icosianComparisonMatrix *ᵥ icosianRealCoordinates w) = _
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    icosianComparison_matrix_gram]
  simp [Matrix.smul_mulVec, dotProduct_smul]

end Atlas.Lattices

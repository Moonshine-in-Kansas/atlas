import Atlas.Fischer.ReflectingFamilyMoments

noncomputable section
namespace Atlas.Fischer

/-- Complex symmetric-square basis in the actual Frobenius symmetric-matrix
realization of the retained normalized Hermitian coordinates. -/
def reflectingFamilyComplexSquareBasis : Module.Basis ReflectingRootParameter ℂ
    (Atlas.Algebra.symmetricMatrixSpace ℂ CoordinateIndex) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun j => Atlas.Algebra.euclideanSymmetricSquare
      (reflectingRootEuclidean (reflectingRootParameterVector j)))
    (reflectingRoot_complex_squares_independent reflectingRootParameterVector
      reflectingRootParameter_isReflectingRoot reflectingRootParameter_distinct_phases)
    (by rw [Atlas.Algebra.symmetricMatrixSpace_finrank, coordinateIndex_card,
      reflectingRootParameter_fintype_card]; norm_num [Nat.choose_two_right])

theorem reflectingFamilyComplexSquareBasis_apply (j : ReflectingRootParameter) :
    reflectingFamilyComplexSquareBasis j = Atlas.Algebra.euclideanSymmetricSquare
      (reflectingRootEuclidean (reflectingRootParameterVector j)) := by
  simp only [reflectingFamilyComplexSquareBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem reflectingFamilySquareBasis_apply (j : ReflectingRootParameter) :
    reflectingFamilySquareBasis j = Atlas.Algebra.symmetricMatrixSquare
      (reflectingRootParameterVector j) :=
  reflectingRootSquareBasis_apply _ _ _ _ j

/-- The actual finite reflecting family uniquely determines the commutative
conjugate-bilinear multiplication from the diagonal equation B(r,r)=10r. -/
theorem reflectingFamily_product_unique
    (B : Coordinates →ₛₗ[starRingEnd Scalar] Coordinates →ₛₗ[starRingEnd Scalar] Coordinates)
    (hB : ∀ x y, B x y = B y x)
    (he : ∀ j : ReflectingRootParameter,
      B (reflectingRootParameterVector j) (reflectingRootParameterVector j) =
        (10 : Scalar) • reflectingRootParameterVector j) :
    ∀ x y, B x y = product x y :=
  reflectingRoot_product_unique reflectingRootParameterVector reflectingRootParameter_isReflectingRoot
    reflectingRootParameter_distinct_phases reflectingRootParameter_fintype_card B hB he

end Atlas.Fischer

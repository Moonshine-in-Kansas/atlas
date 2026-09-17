import Atlas.Fischer.ReflectingRootQuadraticBound
import Atlas.Algebra.SymmetricMatrixScalarExtension

noncomputable section
namespace Atlas.Fischer

/-- The independent squares lie in the actual E-vector space of symmetric
matrices on the retained coordinates. Complex normalization is only a proof tool. -/
theorem reflectingRoot_symmetric_squares_independent {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j = (a.val.val : Scalar) • r i) :
    LinearIndependent Scalar (fun j => Atlas.Algebra.symmetricMatrixSquare (r j)) := by
  apply Atlas.Algebra.symmetricMatrixSquare_independent_of_complex
    (K := Scalar) (I := CoordinateIndex) (J := J) scalarToComplex r cubicMetricScale
  change LinearIndependent ℂ (fun j => Atlas.Algebra.euclideanSymmetricSquare
    (reflectingRootEuclidean (r j)))
  exact reflectingRoot_complex_squares_independent r hr hd

end Atlas.Fischer

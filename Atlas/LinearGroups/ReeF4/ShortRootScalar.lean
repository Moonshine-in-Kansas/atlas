import Atlas.LinearGroups.ReeF4.ShortRootDomain
import Atlas.Algebra.Albert.TraceZeroStabilizerEquiv

/-! The marked short-root operator is defined over the prime field. Its
form preservation therefore gives actual polynomial stabilizer membership. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R] [CharP F 2] [CharP R 2]

theorem shortRootScalarExtension (f : F →+* R) :
    traceZeroScalarExtension (shortRootEquiv (F := F)) f =
      shortRootLinear (F := R) := by
  apply markedBasis.ext
  intro i
  have hm : traceZeroMap f (markedBasis (F := F) i) = markedBasis (F := R) i := by
    cases i with
    | inl i => simp only [markedBasis_diagonal, diagonalVector_map]
    | inr i => simp only [markedBasis_root, rootVector_map]
  rw [← hm, traceZeroScalarExtension_map]
  exact (shortRootLinear_map f _).symm

theorem shortRootEquiv_mem_polynomialStabilizer :
    shortRootEquiv (F := F) ∈ traceZeroPolynomialStabilizer := by
  constructor
  · have h := shortRootLinear_quadratic (universalTraceZero (F := F))
    rw [← shortRootScalarExtension (MvPolynomial.C : F →+*
      MvPolynomial TraceZeroCoordinate F),
      ← evalTwo_traceZeroQuadraticPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h
  · have h := shortRootLinear_cubic (universalTraceZero (F := F))
    rw [← shortRootScalarExtension (MvPolynomial.C : F →+*
      MvPolynomial TraceZeroCoordinate F),
      ← evalTwo_traceZeroCubicPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h

end Atlas.ReeF4

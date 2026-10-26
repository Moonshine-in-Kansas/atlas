import Atlas.LinearGroups.ReeF4.LongRootDomain
import Atlas.Algebra.Albert.TraceZeroStabilizerEquiv

/-! The marked long-root involution is defined over the prime field. Its
form preservation therefore gives actual polynomial stabilizer membership. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R] [CharP F 2] [CharP R 2]

theorem longRootLinear_map (f : F →+* R) (w : TraceZero F) :
    longRootLinear (traceZeroMap f w) = traceZeroMap f (longRootLinear w) := by
  rw [← longRootCoordinateLinear_eq, ← longRootCoordinateLinear_eq]
  apply Subtype.ext
  exact longRootFormula_map f w.val

theorem longRootScalarExtension (f : F →+* R) :
    traceZeroScalarExtension (longRootEquiv (F := F)) f =
      longRootLinear (F := R) := by
  apply markedBasis.ext
  intro i
  have hm : traceZeroMap f (markedBasis (F := F) i) = markedBasis (F := R) i := by
    cases i with
    | inl i => simp only [markedBasis_diagonal, diagonalVector_map]
    | inr i => simp only [markedBasis_root, rootVector_map]
  rw [← hm, traceZeroScalarExtension_map]
  exact (longRootLinear_map f _).symm

theorem longRootEquiv_mem_polynomialStabilizer :
    longRootEquiv (F := F) ∈ traceZeroPolynomialStabilizer := by
  constructor
  · have h := longRootLinear_quadratic (universalTraceZero (F := F))
    rw [← longRootScalarExtension (MvPolynomial.C : F →+*
      MvPolynomial TraceZeroCoordinate F),
      ← evalTwo_traceZeroQuadraticPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h
  · have h := longRootLinear_cubic (universalTraceZero (F := F))
    rw [← longRootScalarExtension (MvPolynomial.C : F →+*
      MvPolynomial TraceZeroCoordinate F),
      ← evalTwo_traceZeroCubicPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h

end Atlas.ReeF4

import Atlas.LinearGroups.ReeF4.WeylStarData
import Atlas.Algebra.Albert.TraceZeroStabilizerEquiv

/-! The source Weyl permutations preserve the actual quadratic and cubic
polynomials, not only their functions on the finite field. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R] [CharP F 2] [CharP R 2]

theorem weylScalarExtension (f : F →+* R) (g : Fin 2) :
    traceZeroScalarExtension (weylOperator (F := F) g) f =
      (weylOperator (F := R) g).toLinearMap := by
  apply markedBasis.ext
  intro i
  have hm : traceZeroMap f (markedBasis (F := F) i) = markedBasis (F := R) i := by
    cases i with
    | inl i => simp only [markedBasis_diagonal, diagonalVector_map]
    | inr i => simp only [markedBasis_root, rootVector_map]
  rw [← hm, traceZeroScalarExtension_map]
  exact weylOperator_map f g _

theorem weylOperator_quadratic (g : Fin 2) (w : TraceZero F) :
    traceZeroQuadratic (weylOperator g w) = traceZeroQuadratic w := by
  fin_cases g
  · exact weylRho_quadratic w
  · exact weylSigma_quadratic w

theorem weylOperator_cubic (g : Fin 2) (w : TraceZero F) :
    traceZeroCubic (weylOperator g w) = traceZeroCubic w := by
  fin_cases g
  · exact weylRho_cubic w
  · exact weylSigma_cubic w

theorem weylOperator_mem_polynomialStabilizer (g : Fin 2) :
    weylOperator (F := F) g ∈ traceZeroPolynomialStabilizer := by
  constructor
  · have h := weylOperator_quadratic g (universalTraceZero (F := F))
    change traceZeroQuadratic ((weylOperator g).toLinearMap
      (universalTraceZero (F := F))) = traceZeroQuadratic (universalTraceZero (F := F)) at h
    rw [← weylScalarExtension (MvPolynomial.C : F →+*
      MvPolynomial TraceZeroCoordinate F),
      ← evalTwo_traceZeroQuadraticPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h
  · have h := weylOperator_cubic g (universalTraceZero (F := F))
    change traceZeroCubic ((weylOperator g).toLinearMap
      (universalTraceZero (F := F))) = traceZeroCubic (universalTraceZero (F := F)) at h
    rw [← weylScalarExtension (MvPolynomial.C : F →+*
      MvPolynomial TraceZeroCoordinate F),
      ← evalTwo_traceZeroCubicPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h

end Atlas.ReeF4

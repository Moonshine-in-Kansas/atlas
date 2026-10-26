import Atlas.Algebra.Albert.TraceZeroPolynomialStabilizer

/-! Scalar extension of the actual quadratic/cubic polynomial stabilizer. -/
noncomputable section
namespace Atlas.Albert
open Matrix
variable {F R : Type*} [CommRing F] [CommRing R]

theorem evalTwo_universalTraceZero (f : F →+* R) (w : TraceZero R) :
    map (MvPolynomial.eval₂Hom f (traceZeroCoordinateEquiv w))
      (universalTraceZero (F:=F) : Carrier (MvPolynomial TraceZeroCoordinate F)) = w := by
  apply Prod.ext
  · funext i
    fin_cases i
    · simp only [map, universalTraceZero, Matrix.cons_val_zero', Matrix.cons_val_succ', MvPolynomial.eval₂Hom_X']
      rfl
    · simp only [map, universalTraceZero, Matrix.cons_val_zero', Matrix.cons_val_succ', MvPolynomial.eval₂Hom_X']
      rfl
    · simp only [map, universalTraceZero, Matrix.cons_val_zero', Matrix.cons_val_succ',
        _root_.map_neg, _root_.map_add, MvPolynomial.eval₂Hom_X']
      change -(w.val.1 0 + w.val.1 1) = w.val.1 2
      have h := w.property
      change w.val.1 0 + w.val.1 1 + w.val.1 2 = 0 at h
      linear_combination -h
  · funext i j
    change MvPolynomial.eval₂Hom f (traceZeroCoordinateEquiv w)
      (MvPolynomial.X (.inr (i,j))) = w.val.2 i j
    rw [MvPolynomial.eval₂Hom_X']
    rfl


theorem evalTwo_traceZeroQuadraticPolynomial (f : F →+* R) (w : TraceZero R) :
    MvPolynomial.eval₂Hom f (traceZeroCoordinateEquiv w)
      (traceZeroQuadraticPolynomial (F:=F)) = traceZeroQuadratic w := by
  rw [traceZeroQuadraticPolynomial, ← quadraticTrace_map, evalTwo_universalTraceZero]
  rfl

theorem evalTwo_traceZeroCubicPolynomial (f : F →+* R) (w : TraceZero R) :
    MvPolynomial.eval₂Hom f (traceZeroCoordinateEquiv w)
      (traceZeroCubicPolynomial (F:=F)) = traceZeroCubic w := by
  rw [traceZeroCubicPolynomial, ← norm_map, evalTwo_universalTraceZero]
  rfl

def traceZeroScalarExtension (g : TraceZero F ≃ₗ[F] TraceZero F) (f : F →+* R) :
    TraceZero R →ₗ[R] TraceZero R :=
  traceZeroCoordinateEquiv.symm.toLinearMap.comp
    ((Matrix.toLin' ((traceZeroMatrixRepresentation g).val.map f)).comp
      traceZeroCoordinateEquiv.toLinearMap)

theorem traceZeroScalarExtension_coordinates (g : TraceZero F ≃ₗ[F] TraceZero F)
    (f : F →+* R) (w : TraceZero R) :
    traceZeroCoordinateEquiv (traceZeroScalarExtension g f w) =
      (traceZeroMatrixRepresentation g).val.map f *ᵥ traceZeroCoordinateEquiv w := by
  simp [traceZeroScalarExtension, Matrix.toLin'_apply]

theorem traceZeroScalarExtension_quadratic
    (g : traceZeroPolynomialStabilizer (F:=F)) (f : F →+* R) (w : TraceZero R) :
    traceZeroQuadratic (traceZeroScalarExtension g.val f w) = traceZeroQuadratic w := by
  have h := congrArg (MvPolynomial.eval₂Hom f (traceZeroCoordinateEquiv w)) g.property.1
  rw [Atlas.PolynomialLinear.eval₂_substitute, ← traceZeroScalarExtension_coordinates,
    evalTwo_traceZeroQuadraticPolynomial, evalTwo_traceZeroQuadraticPolynomial] at h
  exact h

theorem traceZeroScalarExtension_cubic
    (g : traceZeroPolynomialStabilizer (F:=F)) (f : F →+* R) (w : TraceZero R) :
    traceZeroCubic (traceZeroScalarExtension g.val f w) = traceZeroCubic w := by
  have h := congrArg (MvPolynomial.eval₂Hom f (traceZeroCoordinateEquiv w)) g.property.2
  rw [Atlas.PolynomialLinear.eval₂_substitute, ← traceZeroScalarExtension_coordinates,
    evalTwo_traceZeroCubicPolynomial, evalTwo_traceZeroCubicPolynomial] at h
  exact h

end Atlas.Albert

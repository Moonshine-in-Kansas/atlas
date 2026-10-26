import Atlas.LinearGroups.ReeF4.TorusCubic
import Atlas.Algebra.Albert.TraceZeroStabilizerEquiv

/-! Scalar extension and actual polynomial-stabilizer membership of Wilson's
source torus. No finite-field functional-polynomial inference is used. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R] [CharP F 2] [CharP R 2]

theorem torusWeight_map (f : F →+* R) (m : ℕ) (a b : Fˣ) (r : ShortRootLabel) :
    Units.map f.toMonoidHom (torusWeight (G := Fˣ) m a b r) =
      torusWeight (G := Rˣ) m (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) r := by
  simp [torusWeight]

theorem torusEquiv_map (f : F →+* R) (m : ℕ) (a b : Fˣ) (w : TraceZero F) :
    torusEquiv m (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b)
      (traceZeroMap f w) = traceZeroMap f (torusEquiv m a b w) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i j
    change (torusWeight (G := Rˣ) m (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) (i,j) : R) *
      f (w.val.2 i j) = f ((torusWeight (G := Fˣ) m a b (i,j) : F) * w.val.2 i j)
    rw [← torusWeight_map, map_mul]
    rfl

theorem torusScalarExtension (f : F →+* R) (m : ℕ) (a b : Fˣ) :
    traceZeroScalarExtension (torusEquiv m a b) f =
      (torusEquiv m (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b)).toLinearMap := by
  apply markedBasis.ext
  intro i
  have hm : traceZeroMap f (markedBasis (F := F) i) = markedBasis (F := R) i := by
    cases i with
    | inl i => simp only [markedBasis_diagonal, diagonalVector_map]
    | inr i => simp only [markedBasis_root, rootVector_map]
  rw [← hm, traceZeroScalarExtension_map]
  exact (torusEquiv_map f m a b _).symm

theorem torusEquiv_mem_polynomialStabilizer (m : ℕ) (a b : Fˣ) :
    torusEquiv m a b ∈ traceZeroPolynomialStabilizer (F := F) := by
  let f : F →+* MvPolynomial TraceZeroCoordinate F := MvPolynomial.C
  constructor
  · have h := torusEquiv_quadratic m (Units.map f.toMonoidHom a)
      (Units.map f.toMonoidHom b) (universalTraceZero (F := F))
    change traceZeroQuadratic ((torusEquiv m (Units.map f.toMonoidHom a)
      (Units.map f.toMonoidHom b)).toLinearMap (universalTraceZero (F := F))) =
        traceZeroQuadratic (universalTraceZero (F := F)) at h
    rw [← torusScalarExtension f,
      ← evalTwo_traceZeroQuadraticPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h
  · have h := torusEquiv_cubic m (Units.map f.toMonoidHom a)
      (Units.map f.toMonoidHom b) (universalTraceZero (F := F))
    change traceZeroCubic ((torusEquiv m (Units.map f.toMonoidHom a)
      (Units.map f.toMonoidHom b)).toLinearMap (universalTraceZero (F := F))) =
        traceZeroCubic (universalTraceZero (F := F)) at h
    rw [← torusScalarExtension f,
      ← evalTwo_traceZeroCubicPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h

end Atlas.ReeF4

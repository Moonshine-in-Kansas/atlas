import Atlas.Algebra.Albert.TraceZeroBaseChange

/-! The full polynomial stabilizer of Q and C on the trace kernel is isomorphic
to the full polynomial norm-and-unit stabilizer on the Albert space. -/
noncomputable section
namespace Atlas.Albert
open Matrix
variable {F R : Type*} [CommRing F] [CommRing R] [CharP F 2] [CharP R 2]

theorem scalarExtension_traceZeroExtend_norm
    (g : traceZeroPolynomialStabilizer (F:=F)) (f : F →+* R) (x : Carrier R) :
    norm (scalarExtension (traceZeroExtend g.val) f x) = norm x := by
  rw [scalarExtension_traceZeroExtend, traceZeroExtendLinear_apply,
    traceZeroCubicDecomposition, traceZeroScalarExtension_quadratic,
    traceZeroScalarExtension_cubic, ← traceZeroCubicDecomposition,
    traceZero_decomposition]

theorem traceZeroExtend_mem (g : traceZeroPolynomialStabilizer (F:=F)) :
    traceZeroExtend g.val ∈ polynomialStabilizer := by
  refine ⟨?_, traceZeroExtend_unit _⟩
  have h := scalarExtension_traceZeroExtend_norm g
    (MvPolynomial.C : F →+* MvPolynomial Coordinate F) universalVector
  rw [← eval₂_normPolynomial MvPolynomial.C, scalarExtension_coordinates] at h
  have hc : coordinateEquiv (universalVector (F:=F)) = MvPolynomial.X := by
    funext i; cases i <;> rfl
  rw [hc] at h
  exact h

theorem scalarExtension_traceZeroRestrict (g : polynomialStabilizer (F:=F))
    (f : F →+* R) (w : TraceZero R) : scalarExtension g.val f (w : Carrier R) =
      (traceZeroScalarExtension (traceZeroRestrict g) f w : Carrier R) := by
  rw [← traceZeroExtend_restrict g, scalarExtension_traceZeroExtend]
  simp

theorem traceZeroRestrict_scalar_cubic (g : polynomialStabilizer (F:=F))
    (f : F →+* R) (w : TraceZero R) :
    traceZeroCubic (traceZeroScalarExtension (traceZeroRestrict g) f w) =
      traceZeroCubic w := by
  change norm _ = norm _
  rw [← scalarExtension_traceZeroRestrict, scalarExtension_norm]

theorem traceZeroRestrict_scalar_quadratic (g : polynomialStabilizer (F:=F))
    (f : F →+* R) (w : TraceZero R) :
    traceZeroQuadratic (traceZeroScalarExtension (traceZeroRestrict g) f w) =
      traceZeroQuadratic w := by
  rw [traceZeroQuadratic_constantTerm, traceZeroQuadratic_constantTerm,
    ← scalarExtension_traceZeroRestrict, scalarExtension_norm,
    ← scalarExtension_unit g f, ← _root_.map_add, scalarExtension_norm,
    scalarExtension_unit]

theorem universalTraceZero_coordinates :
    traceZeroCoordinateEquiv (universalTraceZero (F:=F)) = MvPolynomial.X := by
  funext i
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => rfl

theorem traceZeroRestrict_mem (g : polynomialStabilizer (F:=F)) :
    traceZeroRestrict g ∈ traceZeroPolynomialStabilizer := by
  constructor
  · have h := traceZeroRestrict_scalar_quadratic g
      (MvPolynomial.C : F →+* MvPolynomial TraceZeroCoordinate F) universalTraceZero
    rw [← evalTwo_traceZeroQuadraticPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h
  · have h := traceZeroRestrict_scalar_cubic g
      (MvPolynomial.C : F →+* MvPolynomial TraceZeroCoordinate F) universalTraceZero
    rw [← evalTwo_traceZeroCubicPolynomial MvPolynomial.C,
      traceZeroScalarExtension_coordinates, universalTraceZero_coordinates] at h
    exact h

def traceZeroStabilizerEquiv : traceZeroPolynomialStabilizer (F:=F) ≃*
    polynomialStabilizer (F:=F) where
  toFun g := ⟨traceZeroExtend g.val, traceZeroExtend_mem g⟩
  invFun g := ⟨traceZeroRestrict g, traceZeroRestrict_mem g⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    exact traceZeroExtend_coe g.val w
  right_inv g := by
    apply Subtype.ext
    exact traceZeroExtend_restrict g
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp [traceZeroExtend]

end Atlas.Albert

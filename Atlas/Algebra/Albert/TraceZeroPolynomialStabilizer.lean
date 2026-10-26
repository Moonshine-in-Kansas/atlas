import Atlas.Algebra.Albert.TraceZeroPolynomial
import Atlas.LinearAlgebra.PolynomialSubstitution

/-! The full stabilizer of the actual quadratic and cubic polynomials on the
26-dimensional trace kernel. This is an algebraic prerequisite, not the Ree group;
no star-product preservation has yet been imposed. -/
noncomputable section
namespace Atlas.Albert
open Matrix
variable {F : Type*} [CommRing F]

def traceZeroCoordinateAut : (TraceZero F ≃ₗ[F] TraceZero F) →*
    ((TraceZeroCoordinate → F) ≃ₗ[F] (TraceZeroCoordinate → F)) where
  toFun g := (traceZeroCoordinateEquiv.symm.trans g).trans traceZeroCoordinateEquiv
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

def traceZeroMatrixRepresentation : (TraceZero F ≃ₗ[F] TraceZero F) →*
    GeneralLinearGroup TraceZeroCoordinate F :=
  ((GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (TraceZeroCoordinate → F))).symm.toMonoidHom).comp
    traceZeroCoordinateAut

theorem traceZeroMatrixRepresentation_apply (g : TraceZero F ≃ₗ[F] TraceZero F)
    (w : TraceZero F) : (traceZeroMatrixRepresentation g).val *ᵥ traceZeroCoordinateEquiv w =
      traceZeroCoordinateEquiv (g w) := by
  change LinearMap.toMatrix' (traceZeroCoordinateAut g).toLinearMap *ᵥ
    traceZeroCoordinateEquiv w = _
  rw [LinearMap.toMatrix'_mulVec]
  simp [traceZeroCoordinateAut]

def traceZeroPolynomialStabilizer : Subgroup (TraceZero F ≃ₗ[F] TraceZero F) :=
  ((Atlas.PolynomialLinear.stabilizer (traceZeroQuadraticPolynomial (F:=F))).comap
    traceZeroMatrixRepresentation) ⊓
  ((Atlas.PolynomialLinear.stabilizer (traceZeroCubicPolynomial (F:=F))).comap
    traceZeroMatrixRepresentation)

theorem mem_traceZeroPolynomialStabilizer (g : TraceZero F ≃ₗ[F] TraceZero F) :
    g ∈ traceZeroPolynomialStabilizer ↔
      Atlas.PolynomialLinear.substitute (traceZeroMatrixRepresentation g).val
        traceZeroQuadraticPolynomial = traceZeroQuadraticPolynomial ∧
      Atlas.PolynomialLinear.substitute (traceZeroMatrixRepresentation g).val
        traceZeroCubicPolynomial = traceZeroCubicPolynomial := Iff.rfl

theorem traceZeroStabilizer_quadratic (g : traceZeroPolynomialStabilizer (F:=F))
    (w : TraceZero F) : traceZeroQuadratic (g.val w) = traceZeroQuadratic w := by
  have h := congrArg (MvPolynomial.eval (traceZeroCoordinateEquiv w)) g.property.1
  rw [Atlas.PolynomialLinear.eval_substitute, traceZeroMatrixRepresentation_apply,
    eval_traceZeroQuadraticPolynomial, eval_traceZeroQuadraticPolynomial] at h
  exact h

theorem traceZeroStabilizer_cubic (g : traceZeroPolynomialStabilizer (F:=F))
    (w : TraceZero F) : traceZeroCubic (g.val w) = traceZeroCubic w := by
  have h := congrArg (MvPolynomial.eval (traceZeroCoordinateEquiv w)) g.property.2
  rw [Atlas.PolynomialLinear.eval_substitute, traceZeroMatrixRepresentation_apply,
    eval_traceZeroCubicPolynomial, eval_traceZeroCubicPolynomial] at h
  exact h

end Atlas.Albert

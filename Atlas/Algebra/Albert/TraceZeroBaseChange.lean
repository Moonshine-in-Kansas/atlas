import Atlas.Algebra.Albert.TraceZeroScalarExtension
import Atlas.Algebra.Albert.TraceZeroRestriction

/-! Compatibility of the trace-kernel splitting with scalar extension. -/
noncomputable section
namespace Atlas.Albert
open Matrix
variable {F R : Type*} [CommRing F] [CommRing R]

def traceZeroMap (f : F →+* R) (w : TraceZero F) : TraceZero R :=
  ⟨map f w, by change trace (map f w) = 0; rw [trace_map, trace_traceZero, f.map_zero]⟩

theorem traceZeroCoordinate_map (f : F →+* R) (w : TraceZero F) :
    traceZeroCoordinateEquiv (traceZeroMap f w) = f ∘ traceZeroCoordinateEquiv w := by
  funext i
  cases i <;> rfl

theorem traceZeroScalarExtension_map (g : TraceZero F ≃ₗ[F] TraceZero F)
    (f : F →+* R) (w : TraceZero F) :
    traceZeroScalarExtension g f (traceZeroMap f w) = traceZeroMap f (g w) := by
  apply traceZeroCoordinateEquiv.injective
  rw [traceZeroScalarExtension_coordinates, traceZeroCoordinate_map, traceZeroCoordinate_map]
  funext i
  exact (f.map_mulVec (traceZeroMatrixRepresentation g).val (traceZeroCoordinateEquiv w) i).symm.trans
    (congrArg (fun y : TraceZeroCoordinate → F => f (y i)) (traceZeroMatrixRepresentation_apply g w))

theorem map_coordinateBasis (f : F →+* R) (i : Coordinate) :
    map f ((coordinateEquiv (F:=F)).symm (Pi.single i 1)) =
      (coordinateEquiv (F:=R)).symm (Pi.single i 1) := by
  apply coordinateEquiv.injective
  rw [coordinate_map, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  funext j
  simp [Pi.single_apply]

theorem linearMap_eq_of_scalarMap {M : Type*} [AddCommGroup M] [Module R M]
    (f : F →+* R) (a b : Carrier R →ₗ[R] M)
    (h : ∀ x : Carrier F, a (map f x) = b (map f x)) : a = b := by
  apply ((Pi.basisFun R Coordinate).map (coordinateEquiv (F:=R)).symm).ext
  intro i
  simpa only [Module.Basis.map_apply, Pi.basisFun_apply, map_coordinateBasis] using
    h ((coordinateEquiv (F:=F)).symm (Pi.single i 1))

variable [CharP F 2] [CharP R 2]

theorem traceZeroProjection_map (f : F →+* R) (x : Carrier F) :
    traceZeroProjection (map f x) = traceZeroMap f (traceZeroProjection x) := by
  apply Subtype.ext
  change map f x - trace (map f x) • unit = map f (x - trace x • unit)
  rw [trace_map]
  apply Prod.ext
  · funext i; simp [traceZeroMap, map, unit]
  · funext i j; simp [traceZeroMap, map, unit]

/-- The unit-line extension makes sense for linear endomorphisms as well. -/
def traceZeroExtendLinear (g : TraceZero R →ₗ[R] TraceZero R) : Carrier R →ₗ[R] Carrier R :=
  (traceZeroSplitEquiv (F:=R)).symm.toLinearMap.comp
    ((LinearMap.prodMap (LinearMap.id : R →ₗ[R] R) g).comp
      traceZeroSplitEquiv.toLinearMap)

@[simp] theorem traceZeroExtendLinear_apply (g : TraceZero R →ₗ[R] TraceZero R)
    (x : Carrier R) : traceZeroExtendLinear g x =
      trace x • unit + (g (traceZeroProjection x) : Carrier R) := rfl

theorem scalarExtension_traceZeroExtend (g : TraceZero F ≃ₗ[F] TraceZero F)
    (f : F →+* R) : scalarExtension (traceZeroExtend g) f =
      traceZeroExtendLinear (traceZeroScalarExtension g f) := by
  apply linearMap_eq_of_scalarMap f
  intro x
  rw [scalarExtension_map, traceZeroExtend_apply, traceZeroExtendLinear_apply,
    trace_map, traceZeroProjection_map, traceZeroScalarExtension_map]
  apply Prod.ext
  · funext i; simp [traceZeroMap, map, unit]
  · funext i j; simp [traceZeroMap, map, unit]

end Atlas.Albert

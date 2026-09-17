import Atlas.Fischer.ProductTraceMaps
import Atlas.Fischer.SignedMonomialGeometry

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Coordinatewise scalar conjugation, or the identity, with no algebra claim. -/
def productTraceCoordinateTwist (b : Bit) :
    Coordinates ≃ₛₗ[(scalarParityAut b).toRingHom] Coordinates where
  toFun x i := scalarParityAut b (x i)
  invFun x i := scalarParityAut b (x i)
  left_inv x := by funext i; exact scalarParityAut_involutive b (x i)
  right_inv x := by funext i; exact scalarParityAut_involutive b (x i)
  map_add' x y := by funext i; exact map_add (scalarParityAut b) (x i) (y i)
  map_smul' a x := by funext i; exact map_mul (scalarParityAut b) a (x i)

theorem productTraceCoordinateTwist_basis (b : Bit) (i : CoordinateIndex) :
    productTraceCoordinateTwist b (coordinateVector i) = coordinateVector i := by
  classical
  funext j
  change scalarParityAut b (coordinateVector i j) = coordinateVector i j
  simp [coordinateVector,Pi.single_apply]

theorem productTraceCoordinateTwist_trace (b : Bit) (f : Coordinates →ₗ[Scalar] Coordinates) :
    LinearMap.trace Scalar Coordinates ((productTraceCoordinateTwist b).conj f) =
      scalarParityAut b (LinearMap.trace Scalar Coordinates f) := by
  rw [coordinateLinearMap_trace,coordinateLinearMap_trace,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearEquiv.conj_apply_apply]
  have hb : (productTraceCoordinateTwist b).symm (coordinateVector i) = coordinateVector i :=
    productTraceCoordinateTwist_basis b i
  rw [hb]
  rfl

/-- Removing the scalar conjugation from a semilinear equivalence is linear. -/
def productTraceLinearFactor (b : Bit)
    (e : Coordinates ≃ₛₗ[(scalarParityAut b).toRingHom] Coordinates) :
    Coordinates ≃ₗ[Scalar] Coordinates where
  toFun x := productTraceCoordinateTwist b (e x)
  invFun x := e.symm (productTraceCoordinateTwist b x)
  left_inv x := by
    change e.symm ((productTraceCoordinateTwist b).symm (productTraceCoordinateTwist b (e x))) = x
    rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
  right_inv x := by
    change productTraceCoordinateTwist b (e (e.symm ((productTraceCoordinateTwist b).symm x))) = x
    rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    funext i
    change scalarParityAut b (e (a • x) i) = a * scalarParityAut b (e x i)
    rw [map_smulₛₗ]
    change scalarParityAut b (scalarParityAut b a * e x i) = _
    rw [map_mul,scalarParityAut_involutive]

/-- Trace is conjugated by the same scalar automorphism as a semilinear change of coordinates. -/
theorem productTrace_semilinear_conj (b : Bit)
    (e : Coordinates ≃ₛₗ[(scalarParityAut b).toRingHom] Coordinates)
    (f : Coordinates →ₗ[Scalar] Coordinates) :
    LinearMap.trace Scalar Coordinates (e.conj f) =
      scalarParityAut b (LinearMap.trace Scalar Coordinates f) := by
  have he : e.conj f = (productTraceCoordinateTwist b).conj
      ((productTraceLinearFactor b e).conj f) := by
    have ht (x : Coordinates) : productTraceCoordinateTwist b (productTraceCoordinateTwist b x) = x := by
      funext i
      exact scalarParityAut_involutive b (x i)
    apply LinearMap.ext
    intro x
    change e (f (e.symm x)) = productTraceCoordinateTwist b (productTraceCoordinateTwist b
      (e (f (e.symm (productTraceCoordinateTwist b (productTraceCoordinateTwist b x))))))
    rw [ht,ht]
  rw [he,productTraceCoordinateTwist_trace,LinearMap.trace_conj']

end Atlas.Fischer

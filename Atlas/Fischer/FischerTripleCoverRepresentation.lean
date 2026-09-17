import Atlas.Fischer.GeneratedCentralExtension
import Atlas.Fischer.ComplexCoordinateExtension

noncomputable section
namespace Atlas.Fischer
open scoped TensorProduct

/-- The actual positive algebra group, retaining its scalar kernel, acts
linearly on the original 783-dimensional coefficient space. -/
def positiveAlgebraLinearEquiv (g : rootGeneratedAlgebraParity.ker) :
    Coordinates ≃ₗ[Scalar] Coordinates where
  toEquiv := g.val.val.val
  map_add' := g.val.val.property.1
  map_smul' a x := by
    have hp : semilinearAlgebraParity g.val.val=0 :=
      congrArg Multiplicative.toAdd g.property
    change g.val.val.val (a • x)=a • g.val.val.val x
    rw [semilinearAlgebraParity_spec,hp,scalarParityAut_zero]

def positiveAlgebraLinearRepresentation :
    rootGeneratedAlgebraParity.ker →* (Coordinates ≃ₗ[Scalar] Coordinates) where
  toFun := positiveAlgebraLinearEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem positiveAlgebraLinearRepresentation_injective :
    Function.Injective positiveAlgebraLinearRepresentation := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact congrArg (fun e : Coordinates ≃ₗ[Scalar] Coordinates => e x) he

theorem positiveAlgebraLinearRepresentation_product (g : rootGeneratedAlgebraParity.ker)
    (x y : Coordinates) :
    positiveAlgebraLinearRepresentation g (product x y)=
      product (positiveAlgebraLinearRepresentation g x) (positiveAlgebraLinearRepresentation g y) :=
  g.val.val.property.2.1 x y

theorem positiveAlgebraLinearRepresentation_scalar (a : Mu3) (x : Coordinates) :
    positiveAlgebraLinearRepresentation (positiveScalarHom a) x=(a.val.val : Scalar) • x := rfl

theorem positiveAlgebraLinearRepresentation_dimension : Module.finrank Scalar Coordinates=783 :=
  coordinates_dimension

theorem displayedRoot_conjugate_linear (t : ReflectingRootParameter) (a : Scalar) (x : Coordinates) :
    (displayedRootAutomorphism t).val (a • x)=star a • (displayedRootAutomorphism t).val x := by
  have hp : semilinearAlgebraParity (displayedRootAutomorphism t)=1 :=
    congrArg Multiplicative.toAdd (displayedAlgebraRootElement_parity t)
  rw [semilinearAlgebraParity_spec,hp,scalarParityAut_one]

/-- The scalar-extension comparison uses exactly the retained embedding of the
coefficient field, not a replacement complex coordinate construction. -/
theorem tripleCover_complex_coordinate_comparison (a : ℝ) (x : Coordinates) (i : CoordinateIndex) :
    realToComplexCoordinates (a ⊗ₜ[ℚ] x) i=a • scalarToComplex (x i) :=
  realToComplexCoordinates_tmul a x i

end Atlas.Fischer

import Atlas.Fischer.FischerTripleCoverCenter
import Atlas.Fischer.FischerTripleCoverRepresentation
import Atlas.Sporadic.Fischer24Prime

noncomputable section
namespace Atlas.Fischer.TripleCover

/-- The actual linear parity kernel in the retained algebra automorphism group. -/
abbrev Model := rootGeneratedAlgebraParity.ker
abbrev Quotient := Atlas.Sporadic.Fischer24Prime.Model
abbrev VectorSpace := Coordinates
abbrev CoefficientField := Scalar
abbrev ScalarKernel := Mu3
abbrev Points := DisplayedReflectingRay
abbrev projection := rootGeneratedPositiveProjection
abbrev scalarEmbedding := positiveScalarHom
abbrev scalarQuotientEquiv := positiveScalarQuotientEquiv
abbrev linearRepresentation := positiveAlgebraLinearRepresentation

theorem finite : Finite Model :=
  Nat.finite_of_card_ne_zero (by rw [rootGeneratedAlgebraPositive_order]; decide)
theorem card : Nat.card Model = 3765617127571985163878400 :=
  rootGeneratedAlgebraPositive_order
theorem order : Nat.card Model = 3 * Nat.card Quotient :=
  rootGeneratedAlgebraPositive_order_triple
theorem perfect : Group.IsPerfect Model := rootGeneratedAlgebraParity_kernel_perfect
theorem projection_surjective : Function.Surjective projection :=
  rootGeneratedPositiveProjection_surjective
theorem scalar_injective : Function.Injective scalarEmbedding := positiveScalarHom_injective
theorem kernel : projection.ker = scalarEmbedding.range := rootGeneratedPositiveProjection_kernel
theorem kernel_card : Nat.card projection.ker = 3 := rootGeneratedPositiveProjection_kernel_card
theorem center : Subgroup.center Model = scalarEmbedding.range := rootGeneratedAlgebraPositive_center
theorem center_card : Nat.card (Subgroup.center Model) = 3 := by
  rw [center, ← kernel, kernel_card]
theorem nonsplit : ¬ ∃ s : Quotient →* Model, projection.comp s = MonoidHom.id _ :=
  rootGeneratedPositiveProjection_nonsplit
theorem representation_injective : Function.Injective linearRepresentation :=
  positiveAlgebraLinearRepresentation_injective
theorem dimension : Module.finrank CoefficientField VectorSpace = 783 :=
  positiveAlgebraLinearRepresentation_dimension
theorem representation_scalar (a : ScalarKernel) (x : VectorSpace) :
    linearRepresentation (scalarEmbedding a) x = (a.val.val : CoefficientField) • x :=
  positiveAlgebraLinearRepresentation_scalar a x
theorem representation_product (g : Model) (x y : VectorSpace) :
    linearRepresentation g (product x y) =
      product (linearRepresentation g x) (linearRepresentation g y) :=
  positiveAlgebraLinearRepresentation_product g x y
/-- The scalar quotient has the faithful projective ray action. -/
theorem quotient_faithful : FaithfulSMul Quotient Points := rootGeneratedRayPositive_faithful
theorem quotient_transitive : MulAction.IsPretransitive Quotient Points :=
  rootGeneratedRayPositive_transitive

structure Construction : Prop where
  finite : Finite Model
  card : Nat.card Model = 3765617127571985163878400
  perfect : Group.IsPerfect Model
  onto : Function.Surjective projection
  kernel : projection.ker = scalarEmbedding.range
  center : Subgroup.center Model = scalarEmbedding.range
  nonsplit : ¬ ∃ s : Quotient →* Model, projection.comp s = MonoidHom.id _
  faithful : Function.Injective linearRepresentation
  dimension : Module.finrank CoefficientField VectorSpace = 783

theorem construction : Construction :=
  ⟨finite, card, perfect, projection_surjective, kernel, center, nonsplit,
    representation_injective, dimension⟩

end Atlas.Fischer.TripleCover

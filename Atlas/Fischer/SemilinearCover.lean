import Atlas.Fischer.TripleCover
import Atlas.Fischer.FischerSemilinearSemidirect
import Atlas.Fischer.FischerScalarInversion

noncomputable section
namespace Atlas.Fischer.SemilinearCover

/-- The full actual semilinear automorphism group of the Conway–Parker algebra. -/
abbrev Model := SemilinearAlgebraAutomorphism
abbrev Quotient := rootGeneratedRayGroup
abbrev LinearCover := TripleCover.Model
abbrev projection := fullSemilinearRayProjection
abbrev scalarEmbedding := scalarAlgebraRepresentation
abbrev scalarQuotientEquiv := fullSemilinearScalarQuotientEquiv
abbrev generatedComparison := generatedAlgebraFullEquiv
abbrev reflectionComplement := rootReflectionComplement
abbrev reflectionAction := rootReflectionPositiveAction
abbrev semidirectEquiv := fullSemilinearSemidirectEquiv

theorem finite : Finite Model := semilinearAlgebraAutomorphism_finite
theorem card : Nat.card Model = 7531234255143970327756800 := fullSemilinearAlgebra_order
theorem order : Nat.card Model = 3 * Nat.card Quotient := fullSemilinearAlgebra_order_triple
theorem projection_surjective : Function.Surjective projection := fullSemilinearRayProjection_surjective
theorem scalar_injective : Function.Injective scalarEmbedding := scalarAlgebraRepresentation_injective
theorem kernel : projection.ker = scalarEmbedding.range := fullSemilinearRayProjection_kernel
theorem kernel_card : Nat.card projection.ker = 3 := by
  rw [kernel, ← Nat.card_congr (MonoidHom.ofInjective scalar_injective).toEquiv, mu3_card]
theorem kernel_not_central : ¬ projection.ker ≤ Subgroup.center Model :=
  fullSemilinearScalarKernel_not_central
theorem reflection_order (t : ReflectingRootParameter) : Nat.card (reflectionComplement t) = 2 :=
  rootReflectionComplement_order t
theorem reflection_scalar_inversion (t : ReflectingRootParameter) (a : Mu3) :
    displayedRootAutomorphism t * scalarEmbedding a * (displayedRootAutomorphism t)⁻¹ =
      scalarEmbedding a⁻¹ := displayedRoot_scalar_conjugation t a
theorem odd_scalar_inversion (g : Model) (hg : semilinearAlgebraParity g = 1) (a : Mu3) :
    g * scalarEmbedding a * g⁻¹ = scalarEmbedding a⁻¹ :=
  oddSemilinear_scalar_conjugation g hg a
theorem reflection_conjugate_linear (t : ReflectingRootParameter) (a : Scalar) (x : Coordinates) :
    (displayedRootAutomorphism t).val (a • x) = star a • (displayedRootAutomorphism t).val x :=
  displayedRoot_conjugate_linear t a x
theorem semidirect_apply (t : ReflectingRootParameter)
    (x : LinearCover ⋊[reflectionAction t] reflectionComplement t) :
    semidirectEquiv t x = x.left.val.val * x.right.val.val :=
  fullSemilinearSemidirectEquiv_apply t x

structure Construction : Prop where
  finite : Finite Model
  card : Nat.card Model = 7531234255143970327756800
  onto : Function.Surjective projection
  kernel : projection.ker = scalarEmbedding.range
  kernel_card : Nat.card projection.ker = 3
  noncentral : ¬ projection.ker ≤ Subgroup.center Model
  split : ∀ t : ReflectingRootParameter,
    Nonempty (LinearCover ⋊[reflectionAction t] reflectionComplement t ≃* Model)

theorem construction : Construction :=
  ⟨finite, card, projection_surjective, kernel, kernel_card, kernel_not_central,
    fun t => ⟨semidirectEquiv t⟩⟩

end Atlas.Fischer.SemilinearCover

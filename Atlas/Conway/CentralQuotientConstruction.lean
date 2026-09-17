import Atlas.Conway.MonomialQuotientSplitting
import Atlas.Lattices.LeechClassTypes

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem leechModTwoRepresentation_classType (g : LeechIsometryGroup) (a : LeechModTwo) :
    leechClassType (leechModTwoRepresentation g a) = leechClassType a := by
  rcases leechClass_partition a with rfl | h | h | h
  · rw [map_zero]
  · exact ((leechClassType_fibers _).2.1.mpr (shellClasses_transport g 4 a h)).trans
      ((leechClassType_fibers a).2.1.mpr h).symm
  · exact ((leechClassType_fibers _).2.2.1.mpr (shellClasses_transport g 6 a h)).trans
      ((leechClassType_fibers a).2.2.1.mpr h).symm
  · exact ((leechClassType_fibers _).2.2.2.mpr (shellClasses_transport g 8 a h)).trans
      ((leechClassType_fibers a).2.2.2.mpr h).symm

theorem quotientModTwoRepresentation_classType (g : LeechCentralQuotient) (a : LeechModTwo) :
    leechClassType (quotientModTwoRepresentation g a) = leechClassType a := by
  obtain ⟨h,rfl⟩ := leechCentralProjection_surjective g
  exact leechModTwoRepresentation_classType h a

theorem golaySignQuotient_card : Nat.card GolaySignQuotient = 2048 := by
  have he := Nat.card_congr quotientMonomialSplitEquiv.toEquiv
  rw [quotientMonomialSubgroup_order] at he
  change Nat.card (GolaySignQuotient ⋊[golaySignQuotientAction] Mathieu24CodeModel) = _ at he
  rw [SemidirectProduct.card,mathieu24_order] at he
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 244823040) he

theorem golaySignProjection_kernel : golaySignProjection.ker = golayOneSubgroup :=
  QuotientGroup.ker_mk' _

structure ConwayCentralQuotientConstruction : Prop where
  center : Subgroup.center LeechIsometryGroup = leechCentralSigns
  center_card : Nat.card leechCentralSigns = 2
  rational_scalar : ∀ g, g ∈ Subgroup.center LeechIsometryGroup →
    ∃ r : ℚ, (r = 1 ∨ r = -1) ∧ ∀ x, rationalExtension g.val x = r • x
  cardinality_relation : 2 * Nat.card LeechCentralQuotient = Nat.card LeechIsometryGroup
  projection_kernel : leechCentralProjection.ker = leechCentralSigns
  split_compatible : ∀ m, (quotientMonomialSplitEquiv (monomialSignQuotientProjection m)).val =
    quotientMonomialEmbedding m
  splitting : quotientMonomialRetraction.comp quotientMonomialSplitting = MonoidHom.id _
  retraction_kernel : quotientMonomialRetraction.ker = quotientMonomialSigns.range
  sign_card : Nat.card GolaySignQuotient = 2048
  monomial_card : Nat.card quotientMonomialSubgroup = 501397585920
  permutations_injective : Function.Injective quotientPermutationEmbedding
  cross_kernel : crossRepresentation.ker = leechCentralSigns
  binary_kernel : leechModTwoRepresentation.ker = leechCentralSigns
  crosses_faithful : Function.Injective quotientCrossRepresentation
  binary_faithful : Function.Injective quotientModTwoRepresentation
  binary_dimension : Module.finrank Bit LeechModTwo = 24
  quadratic : ∀ g a, leechQuadratic (quotientModTwoRepresentation g a) = leechQuadratic a
  minimum_type : ∀ g a, leechClassType (quotientModTwoRepresentation g a) = leechClassType a
  equivariance : ∀ g X, (quotientCrossRepresentation g X).val = quotientModTwoRepresentation g X.val

theorem conway_central_quotient_constructed : ConwayCentralQuotientConstruction where
  center := leechCentralSigns_eq_center.symm
  center_card := leechCentralSigns_card
  rational_scalar := central_rational_scalar
  cardinality_relation := leechCentralQuotient_card_relation
  projection_kernel := leechCentralProjection_kernel
  split_compatible := quotientMonomialSplitEquiv_compatible
  splitting := quotientMonomialRetraction_splitting
  retraction_kernel := quotientMonomialRetraction_kernel
  sign_card := golaySignQuotient_card
  monomial_card := quotientMonomialSubgroup_order
  permutations_injective := quotientPermutationEmbedding_injective
  cross_kernel := crossRepresentation_kernel
  binary_kernel := leechModTwoRepresentation_kernel
  crosses_faithful := quotientCrossRepresentation_injective
  binary_faithful := quotientModTwoRepresentation_injective
  binary_dimension := leechModTwo_finrank
  quadratic := quotientModTwoRepresentation_quadratic
  minimum_type := quotientModTwoRepresentation_classType
  equivariance := quotientCross_modTwo_equivariant

end Atlas.Conway

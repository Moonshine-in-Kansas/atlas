import Atlas.Sporadic.McLaughlinLattice
import Atlas.Lattices.LeechConstruction

noncomputable section
namespace Atlas.Sporadic.McLaughlin
open Atlas.Codes Atlas.Lattices Atlas.Conway
attribute [local instance] Classical.propDecidable

/-- Complete construction on the actual pointwise Leech triangle stabilizer. -/
structure CompleteConstruction : Prop where
  lattice : LeechConstruction
  gram : integerDot vector.val vector.val = 48 ∧ integerDot endpoint.val endpoint.val = 32 ∧
    integerDot vector.val endpoint.val = 24
  finite : Finite Model
  card : Nat.card Model = order
  factorization : Nat.card Model = 2^7 * 3^6 * 5^3 * 7 * 11
  simple : IsSimpleGroup Model
  noncommuting : ∃ g h : Model, g*h ≠ h*g
  perfect : Group.IsPerfect Model
  cover_injective : Function.Injective embedding
  co1_injective : Function.Injective toConway1
  co2_injective : Function.Injective toConway2
  co3_injective : Function.Injective toConway3
  co2_compatible : ∀ g, Conway2.embedding (toConway2 g) = embedding g
  co3_compatible : ∀ g, Conway3.embedding (toConway3 g) = embedding g
  co1_co2_compatible : ∀ g, Conway2.toConway1 (toConway2 g) = toConway1 g
  co1_co3_compatible : ∀ g, Conway3.toConway1 (toConway3 g) = toConway1 g
  norm_four_transport : normFourTransporter.val endpoint = Conway2.vector.val
  complement_rank : Module.finrank ℤ Complement = 22
  complement_free : Module.Free ℤ Complement
  complement_finite : Module.Finite ℤ Complement
  integral_faithful : Function.Injective integralRepresentation
  integral_isometric : ∀ g z t,
    integerDot (integralRepresentation g z).val.val (integralRepresentation g t).val.val =
      integerDot z.val.val t.val.val
  endpoint_surjective : Function.Surjective endpointPermutation
  endpoint_kernel : toPairStabilizer.range = endpointPermutation.ker
  endpoint_derived : commutator PairStabilizer = toPairStabilizer.range
  endpoint_index : 2 * Nat.card Model = Nat.card PairStabilizer
  co3_index : 552 * Nat.card Model = Nat.card Conway3.Model
  degree : Nat.card Points = 275
  graph_transitive : MulAction.IsPretransitive Model Points
  graph_faithful : FaithfulSMul Model Points
  graph_parameters : graph.IsSRGWith 275 112 30 56
  graph_witt : Nonempty (wittGraph ≃g graph)
  graph_distance : ∀ (y z : Points), graph.Adj y z ↔
    integerDot (y.val-z.val).val (y.val-z.val).val = 48
  point_labels_primitive : MulAction.IsPreprimitive McLMathieuModel McLPointLabels
  point_labels_equivariant : ∀ g c,
    mclWittVector (Sum.inl (g • c)) = mathieu22Embedding g • mclWittVector (Sum.inl c)
  point_family_card : Nat.card (Set.range (fun c : McLPointLabels => mclWittVector (Sum.inl c))) = 22
  triangle_degree : Nat.card Triangles = 2025
  triangle_transitive : MulAction.IsPretransitive Model Triangles
  triangle_primitive : MulAction.IsPreprimitive Model Triangles
  triangle_faithful : FaithfulSMul Model Triangles
  triangle_subdegrees : ∀ t : Fin 4,
    Nat.card {y : Triangles // triangleType y = t} = ![1,330,462,1232] t
  triangle_orbits : ∀ x y : Triangles,
    (∃ g : McLMathieuModel, mathieu22Embedding g • x = y) ↔ triangleType x = triangleType y
  mathieu_full : mathieu22Embedding.range = TriangleStabilizer
  mathieu_compatible : ∀ g, (triangleMathieuEquiv g).val = mathieu22Embedding g
  mathieu_order : Nat.card TriangleStabilizer = 443520
  mathieu_maximal : IsCoatom TriangleStabilizer

theorem construction : CompleteConstruction where
  lattice := leech_constructed
  gram := triangle_gram
  finite := finite
  card := card
  factorization := card_factorization
  simple := isSimpleGroup
  noncommuting := exists_mul_ne_mul
  perfect := perfect
  cover_injective := embedding_injective
  co1_injective := toConway1_injective
  co2_injective := toConway2_injective
  co3_injective := toConway3_injective
  co2_compatible := toConway2_compatible
  co3_compatible := toConway3_compatible
  co1_co2_compatible := toConway1_via_conway2
  co1_co3_compatible := toConway1_via_conway3
  norm_four_transport := normFourTransporter_spec
  complement_rank := complement_rank
  complement_free := complement_free
  complement_finite := complement_finite
  integral_faithful := integralRepresentation_injective
  integral_isometric := integralRepresentation_preserves
  endpoint_surjective := endpointPermutation_surjective
  endpoint_kernel := toPairStabilizer_range
  endpoint_derived := pair_commutator_eq_model_image
  endpoint_index := endpoint_index_product
  co3_index := co3_index_product
  degree := degree
  graph_transitive := transitive
  graph_faithful := faithful
  graph_parameters := strongly_regular
  graph_witt := ⟨wittGraphEquiv⟩
  graph_distance := adjacent_iff_distance
  point_labels_primitive := point_labels_primitive
  point_labels_equivariant := point_labels_equivariant
  point_family_card := point_family_card
  triangle_degree := triangle_degree
  triangle_transitive := triangles_transitive
  triangle_primitive := triangles_primitive
  triangle_faithful := triangles_faithful
  triangle_subdegrees := triangle_subdegree
  triangle_orbits := triangle_mathieu_orbits
  mathieu_full := mathieu22Embedding_range
  mathieu_compatible := triangleMathieuEquiv_compatible
  mathieu_order := triangle_stabilizer_card
  mathieu_maximal := triangle_stabilizer_maximal

theorem construction_complete : CompleteConstruction := construction

theorem exists_model : ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model) ∧
    Finite G ∧ Nat.card G = order ∧ IsSimpleGroup G ∧
    (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction :=
  ⟨Model,inferInstance,⟨MulEquiv.refl _⟩,finite,card,isSimpleGroup,exists_mul_ne_mul,construction⟩

end Atlas.Sporadic.McLaughlin

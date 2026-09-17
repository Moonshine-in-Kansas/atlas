import Atlas.Sporadic.HigmanSimsDecompositions
import Atlas.Lattices.LeechConstruction

noncomputable section
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway
attribute [local instance] Classical.propDecidable

/-- Complete construction for the actual full pointwise stabilizer of the marked Leech triangle. -/
structure CompleteConstruction : Prop where
  lattice : LeechConstruction
  gram : integerDot vector.val vector.val = 48 ∧ integerDot endpoint.val endpoint.val = 32 ∧
    integerDot vector.val endpoint.val = 16
  finite : Finite Model
  card : Nat.card Model = 44352000
  factorization : Nat.card Model = 2^9*3^2*5^3*7*11
  simple : IsSimpleGroup Model
  noncommuting : ∃ g h : Model, g*h ≠ h*g
  perfect : Group.IsPerfect Model
  cover_injective : Function.Injective embedding
  co1_injective : Function.Injective toConway1
  co2_injective : Function.Injective toConway2
  co3_injective : Function.Injective toConway3
  norm_four_transport : normFourTransporter.val endpoint = Conway2.vector.val
  co2_compatible : ∀ g, Conway2.embedding (toConway2 g) =
    normFourTransporter*embedding g*normFourTransporter⁻¹
  co3_compatible : ∀ g, Conway3.embedding (toConway3 g) = embedding g
  co1_co2_compatible : ∀ g, Conway2.toConway1 (toConway2 g) =
    leechCentralProjection normFourTransporter*toConway1 g*(leechCentralProjection normFourTransporter)⁻¹
  co1_co3_compatible : ∀ g, Conway3.toConway1 (toConway3 g) = toConway1 g
  co2_index : 953856*Nat.card Model = Nat.card Conway2.Model
  co3_index : 11178*Nat.card Model = Nat.card Conway3.Model
  complement_rank : Module.finrank ℤ Complement = 22
  complement_free : Module.Free ℤ Complement
  complement_finite : Module.Finite ℤ Complement
  integral_faithful : Function.Injective integralRepresentation
  integral_isometric : ∀ g z t,
    integerDot (integralRepresentation g z).val.val (integralRepresentation g t).val.val =
      integerDot z.val.val t.val.val
  sides_card : Nat.card Sides = 11178
  side_parameterization : Function.Bijective hsSideParameterMap
  side_parameters : ∀ t : Fin 5, Nat.card (HSSideParameters co3MarkedCoordinate t) = hsSideSize t
  sides_transitive : MulAction.IsPretransitive Conway3.Model Sides
  side_full_stabilizer : Nonempty (SideStabilizer ≃* Model)
  saturated : Nat.card (MulAction.orbit Conway3.Model baseSide) = 11178 ∧
    Nat.card (MulAction.orbit Model basePoint) = 100
  degree : Nat.card Points = 100
  graph_transitive : MulAction.IsPretransitive Model Points
  graph_primitive : MulAction.IsPreprimitive Model Points
  graph_faithful : FaithfulSMul Model Points
  graph_parameters : graph.IsSRGWith 100 22 0 6
  graph_connected : graph.Connected
  graph_witt : Nonempty (graph ≃g Atlas.Graphs.hexadExtensionGraph
    (mathieu22Blocks co3MarkedCoordinate co3BasePoint) hs_hexad_design_data)
  graph_distance : ∀ u v : Points, graph.Adj u v ↔
    integerDot (u.val-v.val).val (u.val-v.val).val = 48
  graph_nonadjacent : ∀ u v : Points, u ≠ v → ¬graph.Adj u v → integerDot u.val.val v.val.val = 16
  rank_three : Nat.card (MulAction.orbitRel.Quotient PointStabilizer Points) = 3
  subdegrees : ∀ i : Fin 3, Nat.card {y : Points // localFamily y = i} = ![1,22,77] i
  local_transitive : ∀ y z : Points, localFamily y = localFamily z → ∃ g : PointStabilizer, g • y = z
  mathieu_full : mathieu22Embedding.range = PointStabilizer
  mathieu_comparison : Nonempty (MathieuModel ≃* PointStabilizer)
  mathieu_compatible : ∀ g, (pointStabilizerEquiv g).val = mathieu22Embedding g
  mathieu_order : Nat.card PointStabilizer = 443520
  mathieu_simple : IsSimpleGroup PointStabilizer
  mathieu_order_identity : Nat.card Model = 100*Nat.card MathieuModel
  regular_normal_excluded : ∀ N : Subgroup Model, N.Normal →
    MulAction.IsPretransitive N Points →
    (∀ n : N, n • basePoint = basePoint → n = 1) → False
  decomposition_injective : Function.Injective decompositionMap
  decomposition_equivariant : ∀ g y, decompositionMap (g • y) = toConway3 g • decompositionMap y
  decomposition_sizes : Nat.card decompositionSubset = 100 ∧ Nat.card decompositionComplement = 176
  decomposition_invariant : ∀ g D, toConway3 g • D ∈ decompositionSubset ↔ D ∈ decompositionSubset
  complement_invariant : ∀ g D, toConway3 g • D ∈ decompositionComplement ↔ D ∈ decompositionComplement
  decomposition_pairings : ∀ D, D ∈ decompositionSubset ↔
    ∃ v ∈ D.val, integerDot endpoint.val v.val = 16
  complement_pairings : ∀ D, D ∈ decompositionComplement ↔
    ∀ v ∈ D.val, integerDot endpoint.val v.val = 8
  selected_endpoint_unique : ∀ D, D ∈ decompositionSubset →
    ∃! v : leech, v ∈ D.val ∧ integerDot endpoint.val v.val = 16

theorem construction : CompleteConstruction where
  lattice := leech_constructed
  gram := triangle_gram
  finite := finite
  card := card
  factorization := order
  simple := isSimpleGroup
  noncommuting := exists_mul_ne_mul
  perfect := perfect
  cover_injective := embedding_injective
  co1_injective := toConway1_injective
  co2_injective := toConway2_injective
  co3_injective := toConway3_injective
  norm_four_transport := normFourTransporter_spec
  co2_compatible := toConway2_compatible
  co3_compatible := toConway3_compatible
  co1_co2_compatible := toConway1_via_conway2
  co1_co3_compatible := toConway1_via_conway3
  co2_index := co2_index_product
  co3_index := co3_index_product
  complement_rank := complement_rank
  complement_free := complement_free
  complement_finite := complement_finite
  integral_faithful := integralRepresentation_injective
  integral_isometric := integralRepresentation_preserves
  sides_card := sides_card
  side_parameterization := hsSideParameterMap_bijective
  side_parameters := hs_side_parameters_card co3MarkedCoordinate
  sides_transitive := sides_transitive
  side_full_stabilizer := ⟨sideStabilizerEquiv⟩
  saturated := saturated_orbit_bounds
  degree := degree
  graph_transitive := transitive
  graph_primitive := primitive
  graph_faithful := faithful
  graph_parameters := strongly_regular
  graph_connected := connected
  graph_witt := ⟨hsHexadGraphEquiv⟩
  graph_distance := adjacent_iff_distance
  graph_nonadjacent := nonadjacent_inner_product
  rank_three := rank_three
  subdegrees := local_fiber_card
  local_transitive := local_family_transitive
  mathieu_full := mathieu22Embedding_range
  mathieu_comparison := ⟨pointStabilizerEquiv⟩
  mathieu_compatible := pointStabilizerEquiv_compatible
  mathieu_order := point_stabilizer_card
  mathieu_simple := point_stabilizer_simple
  mathieu_order_identity := mathieu22_order_identity
  regular_normal_excluded := fun N hn ht hf => by
    letI := hn
    letI := ht
    exact regular_normal_impossible N hf
  decomposition_injective := decompositionMap_injective
  decomposition_equivariant := decomposition_equivariant
  decomposition_sizes := ⟨decomposition_subset_card,decomposition_complement_card⟩
  decomposition_invariant := decomposition_subset_invariant
  complement_invariant := decomposition_complement_invariant
  decomposition_pairings := decomposition_subset_pairings
  complement_pairings := decomposition_complement_pairings
  selected_endpoint_unique := decomposition_selected_endpoint_unique

theorem construction_complete : CompleteConstruction := construction

theorem exists_model : ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model) ∧
    Finite G ∧ Nat.card G = 44352000 ∧ IsSimpleGroup G ∧
    (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction :=
  ⟨Model,inferInstance,⟨MulEquiv.refl _⟩,finite,card,isSimpleGroup,exists_mul_ne_mul,construction⟩

end Atlas.Sporadic.HigmanSims

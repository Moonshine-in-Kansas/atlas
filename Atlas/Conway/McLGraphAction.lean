import Atlas.Conway.McLGraphDecompositions
import Atlas.GroupTheory.CoprimeNormalTransitivity

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open Atlas.Sporadic.Conway3
open scoped Pointwise
attribute [local instance] Classical.propDecidable

instance mclGraphAction : MulAction McLModel McLGraphPoints :=
  leechTriangleSliceAction (normSixVector co3MarkedCoordinate) mclEndpoint 32 24 16

instance mclComplementAction : MulAction McLModel McLDecompositionComplement :=
  MulAction.compHom _ Atlas.Sporadic.McLaughlin.toPairStabilizer

theorem mcl_graph_complement_equivariant (g : McLModel) (y : McLGraphPoints) :
    mclGraphComplementMap (g • y) = g • mclGraphComplementMap y := by
  apply Subtype.ext
  apply Subtype.ext
  change {g.val.val.val y.val,normSixVector co3MarkedCoordinate-g.val.val.val y.val} =
    ({y.val,normSixVector co3MarkedCoordinate-y.val} : Finset leech).image g.val.val.val
  have hx : g.val.val.val (normSixVector co3MarkedCoordinate) = normSixVector co3MarkedCoordinate := g.val.prop
  simp [Finset.image_insert,Finset.image_singleton,map_sub,hx]

theorem mcl_complement_transitive : MulAction.IsPretransitive McLModel McLDecompositionComplement := by
  letI := finite_points
  letI := point_stabilizer_complement_transitive
  let N := mclEndpointPermutation.ker
  have hn : N.index = 2 := by
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr mcl_endpoint_permutation_surjective,
      Subgroup.card_top,mcl_endpoint_permutation_card]
  have hc : Nat.card McLDecompositionComplement = 275 := by
    rw [SubMulAction.nat_card_ofStabilizer_eq,degree]
  have hcop : Nat.Coprime N.index (Nat.card McLDecompositionComplement) := by
    rw [hn,hc]; decide
  letI := Atlas.GroupTheory.normal_transitive_of_coprime_index N hcop
  constructor
  intro p q
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq N p q
  refine ⟨mclEndpointKernelEquiv n,?_⟩
  change Atlas.Sporadic.McLaughlin.toPairStabilizer (mclEndpointKernelEquiv n) • p = q
  have he : Atlas.Sporadic.McLaughlin.toPairStabilizer (mclEndpointKernelEquiv n) = n.val :=
    congrArg Subtype.val (mclEndpointKernelEquiv.symm_apply_apply n)
  rw [he]
  exact hn

theorem mcl_graph_transitive : MulAction.IsPretransitive McLModel McLGraphPoints := by
  letI := mcl_complement_transitive
  constructor
  intro y z
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq McLModel (mclGraphComplementMap y) (mclGraphComplementMap z)
  refine ⟨g,mcl_graph_complement_injective ?_⟩
  rw [mcl_graph_complement_equivariant,hg]

theorem mcl_graph_faithful : FaithfulSMul McLModel McLGraphPoints where
  eq_of_smul_eq_smul {g h} he := by
    letI := faithful
    apply Atlas.Sporadic.McLaughlin.toConway3_injective
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Points)
    intro p
    by_cases hp : p = basePoint
    · subst p
      exact (Atlas.Sporadic.McLaughlin.toPairStabilizer g).prop.trans
        (Atlas.Sporadic.McLaughlin.toPairStabilizer h).prop.symm
    · obtain ⟨y,hy⟩ := mcl_graph_complement_surjective ⟨p,hp⟩
      have hh := congrArg mclGraphComplementMap (he y)
      rw [mcl_graph_complement_equivariant,mcl_graph_complement_equivariant,hy] at hh
      exact congrArg Subtype.val hh

end Atlas.Conway

import Atlas.Conway.Co3Decompositions

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def co3PointHeptadMap (a : Omega) (g : Mathieu23PointModel a) :
    Co3PointHeptad a → Co3PointHeptad a
  | Sum.inl b => Sum.inl (g • b)
  | Sum.inr B => Sum.inr ⟨mathieu23PermuteBlock a g B.val,mathieu23Blocks_preserved a g B.val B.prop⟩

theorem co3EvenEndpoint_equivariant (a : Omega) (g : Mathieu23PointModel a)
    (p : Co3PointHeptad a) :
    (co3EvenEndpointMap a (co3PointHeptadMap a g p)).val =
      (permutationEmbedding g.val).val (co3EvenEndpointMap a p).val := by
  apply Subtype.ext
  cases p with
  | inl b =>
    change (co3PointEndpoint a (g • b)).val.val =
      integerPermutation g.val.val (co3PointEndpoint a b).val.val
    rw [co3PointEndpoint_coordinates,co3PointEndpoint_coordinates,permutation_constantSupport]
    congr 1
    have hg : g.val.val a = a := g.prop
    simp [permuteBlock,hg]
    rfl
  | inr B =>
    change constantSupportVector 2 (insert a (mathieu23BlockLift a (mathieu23PermuteBlock a g B.val))) =
      integerPermutation g.val.val (constantSupportVector 2 (insert a (mathieu23BlockLift a B.val)))
    rw [permutation_constantSupport,mathieu23BlockLift_permute]
    have hg : g.val.val a = a := g.prop
    simp [permuteBlock,hg]

theorem co3PointHeptadDecomposition_equivariant (a : Omega) (g : Mathieu23PointModel a)
    (p : Co3PointHeptad a) :
    co3PointHeptadDecompositionEquiv a (co3PointHeptadMap a g p) =
      mathieu23ToNormSixStabilizer a g • co3PointHeptadDecompositionEquiv a p := by
  apply Subtype.ext
  change { (co3EvenEndpointMap a (co3PointHeptadMap a g p)).val,
      normSixVector a-(co3EvenEndpointMap a (co3PointHeptadMap a g p)).val } =
    ({(co3EvenEndpointMap a p).val,normSixVector a-(co3EvenEndpointMap a p).val} : Finset leech).image
      (permutationEmbedding g.val).val
  rw [co3EvenEndpoint_equivariant]
  have hg : (permutationEmbedding g.val).val (normSixVector a) = normSixVector a :=
    (mathieu23ToNormSixStabilizer a g).prop
  simp [map_sub,hg]

end Atlas.Conway

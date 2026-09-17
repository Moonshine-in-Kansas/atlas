import Atlas.Fischer.GeneratedPositiveEdges
import Atlas.Fischer.GeneratedRayParity
import Atlas.Algebra.CoprimeGenerationPerfect

noncomputable section
namespace Atlas.Fischer

/-- Independent unit-edge and zero-edge generation forces perfectness of the
actual linear subgroup, before any group-order calculation. -/
theorem rootGeneratedAlgebraParity_kernel_perfect : Group.IsPerfect rootGeneratedAlgebraParity.ker := by
  let S : Set rootGeneratedAlgebraParity.ker :=
    rootGeneratedAlgebraParity.ker.subtype ⁻¹' rootGeneratedAlgebraEdgePairs reflectingUnitGraph
  let T : Set rootGeneratedAlgebraParity.ker := rootGeneratedAlgebraParity.ker.subtype ⁻¹'
    rootGeneratedAlgebraEdgePairs (reflectingZeroGraph reflectingRootParameterVector)
  have hunit := rootGeneratedAlgebraParity_kernel_edges reflectingUnitGraph reflectingUnitGraph_connected
  have hzero := rootGeneratedAlgebraParity_kernel_edges (reflectingZeroGraph reflectingRootParameterVector)
    reflectingFamily_zero_graph_connected
  have hs : Subgroup.closure S=⊤ := by
    exact Atlas.Algebra.subgroup_preimage_generates_of_closure_eq _ _ hunit.symm
  have ht : Subgroup.closure T=⊤ := by
    exact Atlas.Algebra.subgroup_preimage_generates_of_closure_eq _ _ hzero.symm
  apply Atlas.Algebra.perfect_of_two_three_generating_sets S T hs ht
  · rintro g ⟨i,j,hij,hg⟩
    apply Subtype.ext
    change g.val^2=1
    change g.val=displayedAlgebraRootElement i * displayedAlgebraRootElement j at hg
    rw [hg]
    exact displayedAlgebraRootElement_unit_square i j hij.2
  · rintro g ⟨i,j,hij,hg⟩
    apply Subtype.ext
    change g.val^3=1
    change g.val=displayedAlgebraRootElement i * displayedAlgebraRootElement j at hg
    rw [hg]
    exact displayedAlgebraRootElement_zero_cube i j hij.2

/-- The actual projection restricts to the two positive subgroups. -/
def rootGeneratedPositiveProjection : rootGeneratedAlgebraParity.ker →* rootGeneratedRayParity.ker :=
  (rootGeneratedRayProjection.comp rootGeneratedAlgebraParity.ker.subtype).codRestrict
    rootGeneratedRayParity.ker (fun e => by
      change rootGeneratedRayParity (rootGeneratedRayProjection e.val)=1
      rw [rootGeneratedRayParity_projection]
      exact e.property)

theorem rootGeneratedPositiveProjection_surjective : Function.Surjective rootGeneratedPositiveProjection := by
  intro g
  obtain ⟨e,he⟩ := rootGeneratedRayProjection_surjective g.val
  have hp : e ∈ rootGeneratedAlgebraParity.ker := by
    change rootGeneratedAlgebraParity e=1
    rw [← rootGeneratedRayParity_projection,he]
    exact g.property
  exact ⟨⟨e,hp⟩,Subtype.ext he⟩

/-- Perfectness passes through the actual scalar projection, without assuming
simplicity or a target group order. -/
theorem rootGeneratedRayParity_kernel_perfect : Group.IsPerfect rootGeneratedRayParity.ker := by
  letI : Group.IsPerfect rootGeneratedAlgebraParity.ker := rootGeneratedAlgebraParity_kernel_perfect
  exact Group.IsPerfect.ofSurjective rootGeneratedPositiveProjection_surjective

end Atlas.Fischer

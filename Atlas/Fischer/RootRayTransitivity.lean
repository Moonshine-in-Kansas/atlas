import Atlas.Fischer.GeneratedRootGroups
import Atlas.Fischer.ReflectingFamilyGraph

noncomputable section
namespace Atlas.Fischer

def displayedRayOfParameter (t : ReflectingRootParameter) : DisplayedReflectingRay :=
  ⟨reflectingRootParameterRay t,⟨t,rfl⟩⟩

theorem displayedRayOfParameter_surjective : Function.Surjective displayedRayOfParameter := by
  rintro ⟨R,t,ht⟩
  exact ⟨t,Subtype.ext ht⟩

theorem semilinearDisplayedRayAction_parameter_value (e : SemilinearAlgebraAutomorphism)
    (t : ReflectingRootParameter) :
    (semilinearDisplayedRayAction e (displayedRayOfParameter t)).val =
      rootRay (e.val (reflectingRootParameterVector t)) :=
  semilinearAlgebra_rootRay_map e _

theorem displayedRootRayInvolution_parameter_value (i j : ReflectingRootParameter) :
    (displayedRootRayInvolution i (displayedRayOfParameter j)).val =
      rootRay (rootMap (reflectingRootParameterVector i) (reflectingRootParameterVector j)) :=
  semilinearDisplayedRayAction_parameter_value _ _

/-- Across an actual zero-pairing edge, two generating root involutions carry
one endpoint to the other. -/
theorem displayedRootRay_zero_edge (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=0) :
    (displayedRootRayInvolution i * displayedRootRayInvolution j) (displayedRayOfParameter i) =
      displayedRayOfParameter j := by
  apply Subtype.ext
  rw [displayedRootRayInvolution,displayedRootRayInvolution,← map_mul,
    semilinearDisplayedRayAction_parameter_value]
  change rootRay (rootMap (reflectingRootParameterVector i)
    (rootMap (reflectingRootParameterVector j) (reflectingRootParameterVector i))) = _
  have hs : hermitian (reflectingRootParameterVector j) (reflectingRootParameterVector i)=0 := by
    rw [← hermitian_star,h,star_zero]
  rw [rootMap_zero_pairing _ _ hs,product_comm (reflectingRootParameterVector j),
    ← rootMap_zero_pairing _ _ h,(reflectingRootParameter_isReflectingRoot i).2.2.1]
  rfl

theorem rootGeneratedRayGroup_parameter_transitive (i j : ReflectingRootParameter) :
    ∃ g : rootGeneratedRayGroup, g.val (displayedRayOfParameter i)=displayedRayOfParameter j := by
  obtain ⟨w⟩ := reflectingFamily_zero_graph_connected i j
  induction w with
  | nil => exact ⟨1,rfl⟩
  | @cons a b c h w ih =>
    obtain ⟨g,hg⟩ := ih
    let e : rootGeneratedRayGroup :=
      ⟨displayedRootRayInvolution a * displayedRootRayInvolution b,
        rootGeneratedRayGroup.mul_mem (displayedRootRayInvolution_mem a) (displayedRootRayInvolution_mem b)⟩
    refine ⟨g*e,?_⟩
    change g.val (e.val (displayedRayOfParameter a))=displayedRayOfParameter c
    rw [show e.val (displayedRayOfParameter a)=displayedRayOfParameter b from
      displayedRootRay_zero_edge a b h.2,hg]

/-- Transitivity follows from the previously verified connected zero graph,
without a frame stabilizer or an order calculation. -/
theorem rootGeneratedRayGroup_transitive (R S : DisplayedReflectingRay) :
    ∃ g : rootGeneratedRayGroup, g.val R=S := by
  obtain ⟨i,rfl⟩ := displayedRayOfParameter_surjective R
  obtain ⟨j,rfl⟩ := displayedRayOfParameter_surjective S
  exact rootGeneratedRayGroup_parameter_transitive i j

instance displayedReflectingRayFinite : Finite DisplayedReflectingRay :=
  Finite.of_surjective displayedRayOfParameter displayedRayOfParameter_surjective

instance rootGeneratedRayGroupFinite : Finite rootGeneratedRayGroup := inferInstance

/-- Faithfulness belongs to the actual derived permutation subgroup. -/
theorem rootGeneratedRayGroup_faithful (g h : rootGeneratedRayGroup)
    (he : ∀ R, g.val R=h.val R) : g=h := by
  apply Subtype.ext
  exact Equiv.ext he

end Atlas.Fischer

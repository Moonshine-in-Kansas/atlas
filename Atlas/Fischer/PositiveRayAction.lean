import Atlas.Fischer.GeneratedDerivedSubgroups
import Atlas.Fischer.RootRayClassInterface
import Atlas.GroupTheory.PrimitiveIndexTwoSimplicity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem rootGeneratedRayPositive_transitive :
    MulAction.IsPretransitive rootGeneratedRayParity.ker DisplayedReflectingRay := by
  haveI : MulAction.IsPretransitive rootGeneratedRayGroup DisplayedReflectingRay :=
    MulAction.IsPretransitive.mk rootGeneratedRayGroup_transitive
  let t : ReflectingRootParameter := .inl (Classical.arbitrary Omega)
  have hd : distinguishedRootElement t ∉ rootGeneratedRayParity.ker := by
    intro h
    change rootGeneratedRayParity (distinguishedRootElement t) = 1 at h
    rw [distinguishedRootElement_parity] at h
    exact (by decide : Multiplicative.ofAdd (1 : Bit) ≠ 1) h
  exact Atlas.GroupTheory.index_two_transitive_of_outside_fixed rootGeneratedRayParity.ker
    rootGeneratedRayParity_index (distinguishedRootElement t) hd
    (distinguishedRootElement_mul_self t) (displayedRayOfParameter t)
    (displayedRootRayInvolution_self t)

 theorem rootGeneratedRayPositive_faithful :
    FaithfulSMul rootGeneratedRayParity.ker DisplayedReflectingRay := inferInstance

end Atlas.Fischer

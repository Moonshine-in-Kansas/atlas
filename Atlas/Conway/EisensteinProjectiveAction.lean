import Atlas.Conway.EisensteinProjectiveModel
import Atlas.Conway.EisensteinStandardFrame

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem eisensteinIntegralAction_unit (u : Eisensteinˣ) (x : EisensteinLattice) :
    eisensteinIntegralAction (eisensteinUnitIsometries u) x = (u : Eisenstein) • x := by
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  rw [eisensteinIntegralAction_agrees, eisensteinUnitIsometries_apply]
  exact (eisensteinCoordinateEmbedding_smul _ _).symm

/-- Every scalar unit fixes every intrinsic frame; no converse is asserted here. -/
theorem eisensteinUnitIsometries_frame (u : Eisensteinˣ) (F : EisensteinFrame) :
    eisensteinUnitIsometries u • F = F := by
  obtain ⟨c, hc, he⟩ := eisensteinFrame_pair F
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
  apply Subtype.ext
  change F.val.image (eisensteinClassAction (eisensteinUnitIsometries u)) = F.val
  rw [he, eisensteinClassAction_pair, eisensteinClassAction_mk, eisensteinIntegralAction_unit]
  exact eisensteinClass_unit_pair u x.val

theorem eisensteinScalarSubgroup_frame_kernel :
    eisensteinScalarSubgroup ≤ (MulAction.toPermHom eisensteinHermitianGroup EisensteinFrame).ker := by
  intro g hg
  rw [← eisensteinUnitIsometries_range] at hg
  obtain ⟨u, rfl⟩ := hg
  apply Equiv.ext
  exact eisensteinUnitIsometries_frame u

/-- The frame permutation representation descends through the six scalar units. -/
def eisensteinQuotientFrameHom : EisensteinHermitianQuotient →* Equiv.Perm EisensteinFrame :=
  QuotientGroup.lift _ (MulAction.toPermHom eisensteinHermitianGroup EisensteinFrame)
    eisensteinScalarSubgroup_frame_kernel

/-- The descended representation of the quotient of the actual Co0 centralizer. -/
def eisensteinProjectiveFrameHom : EisensteinProjectiveModel →* Equiv.Perm EisensteinFrame :=
  eisensteinQuotientFrameHom.comp eisensteinProjectiveComparison.symm.toMonoidHom

instance eisensteinProjectiveFrameAction : MulAction EisensteinProjectiveModel EisensteinFrame :=
  MulAction.compHom _ eisensteinProjectiveFrameHom

theorem eisensteinProjectiveFrameAction_mk (g : eisensteinHermitianGroup) (F : EisensteinFrame) :
    (QuotientGroup.mk (eisensteinCentralizerEquiv g) : EisensteinProjectiveModel) • F = g • F := by
  change eisensteinQuotientFrameHom
    (eisensteinProjectiveComparison.symm (QuotientGroup.mk (eisensteinCentralizerEquiv g))) F = _
  rw [← eisensteinProjectiveComparison_mk, eisensteinProjectiveComparison.symm_apply_apply]
  rfl

end Atlas.Conway

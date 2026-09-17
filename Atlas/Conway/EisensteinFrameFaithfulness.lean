import Atlas.Conway.EisensteinProjectiveFusion
import Atlas.Conway.EisensteinTriadOrbit
import Atlas.GroupTheory.LocalFusionFaithfulness

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction

/-- The actual local quotient acts nontrivially, as witnessed by its triad orbit. -/
theorem eisensteinLocalProjective_moves : ∃ F : EisensteinFrame, ∃ h : TernaryLocalPhaseGroup,
    eisensteinLocalProjectiveEmbedding h • F ≠ F := by
  obtain ⟨F, hF, G, hG, hne⟩ := Finset.one_lt_card.mp
    (show 1 < eisensteinTriadFamily.card by rw [eisensteinTriadFamily_card]; decide)
  obtain ⟨g, hg⟩ := eisensteinTriadFamily_transitive F G hF hG
  refine ⟨F, eisensteinFrameModuloScalarsEquiv (QuotientGroup.mk g), ?_⟩
  rw [eisensteinLocalProjectiveEmbedding_mk, eisensteinProjectiveFrameAction_mk]
  exact fun h => hne (h.symm.trans hg)

/-- The scalar quotient action is faithful. This uses actual local normal
subgroups, one Fourier fusion, and the165 orbit, without assuming transitivity. -/
theorem eisensteinProjectiveFrame_kernel :
    (toPermHom EisensteinProjectiveModel EisensteinFrame).ker = ⊥ := by
  obtain ⟨F, h, hm⟩ := eisensteinLocalProjective_moves
  exact Atlas.GroupTheory.action_kernel_eq_bot_of_local_fusion
    eisensteinLocalProjectiveEmbedding eisensteinStandardFrame
    eisensteinLocalProjectiveEmbedding_range ternaryLocalPhaseNormal
    (fun N hN => @ternaryLocalPhase_normal_subgroups N hN)
    eisensteinProjectiveFusionInput eisensteinProjectiveFusionOutput
    eisensteinProjectiveFusionInput_mem eisensteinProjectiveFusionOutput_not_mem
    (eisensteinProjectiveProjection eisensteinFourierIsometry)
    eisensteinProjective_fusion F h hm

instance eisensteinProjectiveFrame_faithful : FaithfulSMul EisensteinProjectiveModel EisensteinFrame where
  eq_of_smul_eq_smul h := by
    apply (MonoidHom.ker_eq_bot_iff (toPermHom EisensteinProjectiveModel EisensteinFrame)).mp
      eisensteinProjectiveFrame_kernel
    exact Equiv.ext h

/-- The full linear frame-action kernel is exactly the six scalar isometries. -/
theorem eisensteinHermitianFrame_kernel :
    (toPermHom eisensteinHermitianGroup EisensteinFrame).ker = eisensteinScalarSubgroup := by
  apply le_antisymm _ eisensteinScalarSubgroup_frame_kernel
  intro g hg
  have hp : eisensteinProjectiveProjection g = 1 := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := EisensteinFrame)
    intro F
    change (QuotientGroup.mk (eisensteinCentralizerEquiv g) : EisensteinProjectiveModel) • F = 1 • F
    rw [eisensteinProjectiveFrameAction_mk, one_smul]
    exact congrArg (fun p : Equiv.Perm EisensteinFrame => p F) hg
  have hc : eisensteinCentralizerEquiv g ∈ eisensteinCentralizerScalars :=
    (QuotientGroup.eq_one_iff _).mp hp
  obtain ⟨s, hs, he⟩ := hc
  exact eisensteinCentralizerEquiv.injective he ▸ hs

end Atlas.Conway

import Atlas.Conway.EisensteinLocalQuotientEmbedding
import Atlas.Conway.EisensteinFourierFusion

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

def eisensteinProjectiveProjection : eisensteinHermitianGroup →* EisensteinProjectiveModel :=
  (QuotientGroup.mk' eisensteinCentralizerScalars).comp eisensteinCentralizerEquiv.toMonoidHom

theorem eisensteinLocalProjectiveEmbedding_quotient (g : eisensteinCoordinateFrameStabilizer) :
    eisensteinLocalProjectiveEmbedding (eisensteinFramePhaseQuotient g) =
      eisensteinProjectiveProjection g.val := by
  have h := eisensteinLocalProjectiveEmbedding_mk g
  exact h

theorem eisensteinLocalProjectiveEmbedding_abstract (a : EisensteinFrameAbstractGroup) :
    eisensteinLocalProjectiveEmbedding (eisensteinAbstractPhaseQuotient a) =
      eisensteinProjectiveProjection (eisensteinFrameAbstractHom a) := by
  have h := eisensteinLocalProjectiveEmbedding_quotient (eisensteinFullFrameGroupEquiv a)
  change eisensteinLocalProjectiveEmbedding
    (eisensteinAbstractPhaseQuotient (eisensteinFullFrameGroupEquiv.symm
      (eisensteinFullFrameGroupEquiv a))) = _ at h
  rw [eisensteinFullFrameGroupEquiv.symm_apply_apply] at h
  exact h

def eisensteinLocalFromCode (t : ternaryGolay) (p : TernaryPureAutomorphism) :
    TernaryLocalPhaseGroup := ⟨Multiplicative.ofAdd (Submodule.Quotient.mk t), p⟩

theorem eisensteinLocalProjectiveEmbedding_code (t : ternaryGolay) (p : TernaryPureAutomorphism) :
    eisensteinLocalProjectiveEmbedding (eisensteinLocalFromCode t p) =
      eisensteinProjectiveProjection
        (eisensteinPhaseIsometries (Multiplicative.ofAdd t) * eisensteinCoordinateIsometries p) := by
  have h := eisensteinLocalProjectiveEmbedding_abstract
    (1, ⟨Multiplicative.ofAdd t, p⟩)
  change eisensteinLocalProjectiveEmbedding (eisensteinLocalFromCode t p) =
    eisensteinProjectiveProjection (eisensteinFrameAbstractHom (1, ⟨Multiplicative.ofAdd t, p⟩)) at h
  simpa [eisensteinFrameAbstractHom, eisensteinSignHom, eisensteinCodeSemidirectIsometries] using h

def eisensteinProjectiveFusionInput : TernaryLocalPhaseGroup :=
  eisensteinLocalFromCode eisensteinFusionInput 1

def eisensteinProjectiveFusionOutput : TernaryLocalPhaseGroup :=
  eisensteinLocalFromCode eisensteinFusionOutput
    ⟨eisensteinFusionPermutation, eisensteinFusionPermutation_mem⟩

theorem eisensteinProjective_fusion :
    eisensteinProjectiveProjection eisensteinFourierIsometry *
      eisensteinLocalProjectiveEmbedding eisensteinProjectiveFusionInput *
        (eisensteinProjectiveProjection eisensteinFourierIsometry)⁻¹ =
      eisensteinLocalProjectiveEmbedding eisensteinProjectiveFusionOutput := by
  rw [eisensteinProjectiveFusionInput, eisensteinProjectiveFusionOutput,
    eisensteinLocalProjectiveEmbedding_code, eisensteinLocalProjectiveEmbedding_code]
  rw [map_one, mul_one, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg eisensteinProjectiveProjection eisensteinFourier_fusion_group

theorem eisensteinProjectiveFusionInput_mem :
    eisensteinProjectiveFusionInput ∈ ternaryLocalPhaseNormal := by
  exact ⟨Multiplicative.ofAdd (Submodule.Quotient.mk eisensteinFusionInput), rfl⟩

theorem eisensteinProjectiveFusionOutput_not_mem :
    eisensteinProjectiveFusionOutput ∉ ternaryLocalPhaseNormal := by
  rintro ⟨v, hv⟩
  have h := congrArg (fun z : TernaryLocalPhaseGroup => z.right.val) hv
  exact eisensteinFusionPermutation_ne_one h.symm

end Atlas.Conway

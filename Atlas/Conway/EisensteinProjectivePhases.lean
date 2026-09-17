import Atlas.Conway.EisensteinFrameFaithfulness

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction

def eisensteinProjectivePhases : Subgroup EisensteinProjectiveModel :=
  ternaryLocalPhaseNormal.map eisensteinLocalProjectiveEmbedding

theorem eisensteinProjectivePhases_le_stabilizer :
    eisensteinProjectivePhases ≤ stabilizer EisensteinProjectiveModel eisensteinStandardFrame := by
  rw [← eisensteinLocalProjectiveEmbedding_range]
  exact Subgroup.map_le_range _ _

theorem eisensteinProjectivePhases_abelian : IsMulCommutative eisensteinProjectivePhases := by
  apply IsMulCommutative.of_comm
  rintro ⟨g, ⟨e, ⟨v, rfl⟩, rfl⟩⟩ ⟨h, ⟨f, ⟨w, rfl⟩, rfl⟩⟩
  apply Subtype.ext
  change eisensteinLocalProjectiveEmbedding (SemidirectProduct.inl v) *
    eisensteinLocalProjectiveEmbedding (SemidirectProduct.inl w) =
      eisensteinLocalProjectiveEmbedding (SemidirectProduct.inl w) *
        eisensteinLocalProjectiveEmbedding (SemidirectProduct.inl v)
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm v w]

theorem eisensteinProjectivePhases_card : Nat.card eisensteinProjectivePhases = 243 := by
  unfold eisensteinProjectivePhases
  rw [← Nat.card_congr (ternaryLocalPhaseNormal.equivMapOfInjective
    eisensteinLocalProjectiveEmbedding eisensteinLocalProjectiveEmbedding_injective).toEquiv]
  have he := MonoidHom.ofInjective (SemidirectProduct.inl_injective
    (φ := ternaryPhaseMultiplicativeAction))
  change Nat.card (SemidirectProduct.inl : Multiplicative TernaryPhaseModule →*
    TernaryLocalPhaseGroup).range = 243
  rw [← Nat.card_congr he.toEquiv]
  exact ternaryPhaseModule_card

/-- Actual Fourier fusion forces every normal subgroup containing the phases
to contain the entire local stabilizer. -/
theorem eisensteinLocal_le_normal_of_phases (L : Subgroup EisensteinProjectiveModel)
    [L.Normal] (hL : eisensteinProjectivePhases ≤ L) :
    eisensteinLocalProjectiveEmbedding.range ≤ L := by
  apply Atlas.GroupTheory.range_le_normal_of_local_fusion
    eisensteinLocalProjectiveEmbedding ternaryLocalPhaseNormal
    (fun N hN => @ternaryLocalPhase_normal_subgroups N hN)
    eisensteinProjectiveFusionInput eisensteinProjectiveFusionOutput
    eisensteinProjectiveFusionInput_mem eisensteinProjectiveFusionOutput_not_mem
    (eisensteinProjectiveProjection eisensteinFourierIsometry) eisensteinProjective_fusion L
  intro e he
  exact hL ⟨e, he, rfl⟩

theorem eisensteinLocal_le_phase_normalClosure :
    eisensteinLocalProjectiveEmbedding.range ≤
      Subgroup.normalClosure (eisensteinProjectivePhases : Set EisensteinProjectiveModel) :=
  eisensteinLocal_le_normal_of_phases _ Subgroup.le_normalClosure

end Atlas.Conway

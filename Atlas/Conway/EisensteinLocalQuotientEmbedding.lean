import Atlas.Conway.EisensteinProjectiveAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- The quotient of the full frame stabilizer embeds in the full scalar quotient. -/
def eisensteinLocalQuotientMap :
    (eisensteinCoordinateFrameStabilizer ⧸ eisensteinFrameScalarSubgroup) →*
      EisensteinHermitianQuotient :=
  QuotientGroup.map _ _ eisensteinCoordinateFrameStabilizer.subtype
    eisensteinFrameScalarSubgroup_comap.ge

theorem eisensteinLocalQuotientMap_injective : Function.Injective eisensteinLocalQuotientMap := by
  apply (MonoidHom.ker_eq_bot_iff eisensteinLocalQuotientMap).mp
  rw [eisensteinLocalQuotientMap, QuotientGroup.ker_map,
    eisensteinFrameScalarSubgroup_comap, QuotientGroup.map_mk'_self]

/-- The actual 3^5:M11 group as a subgroup of the actual centralizer/scalar quotient. -/
def eisensteinLocalProjectiveEmbedding : TernaryLocalPhaseGroup →* EisensteinProjectiveModel :=
  eisensteinProjectiveComparison.toMonoidHom.comp
    (eisensteinLocalQuotientMap.comp eisensteinFrameModuloScalarsEquiv.symm.toMonoidHom)

theorem eisensteinLocalProjectiveEmbedding_injective :
    Function.Injective eisensteinLocalProjectiveEmbedding :=
  eisensteinProjectiveComparison.injective.comp
    (eisensteinLocalQuotientMap_injective.comp eisensteinFrameModuloScalarsEquiv.symm.injective)

theorem eisensteinLocalProjectiveEmbedding_mk (g : eisensteinCoordinateFrameStabilizer) :
    eisensteinLocalProjectiveEmbedding (eisensteinFrameModuloScalarsEquiv (QuotientGroup.mk g)) =
      QuotientGroup.mk (eisensteinCentralizerEquiv g.val) := by
  change eisensteinProjectiveComparison (eisensteinLocalQuotientMap
    (eisensteinFrameModuloScalarsEquiv.symm (eisensteinFrameModuloScalarsEquiv
      (QuotientGroup.mk g)))) = _
  rw [eisensteinFrameModuloScalarsEquiv.symm_apply_apply]
  rfl

/-- The local group is the entire stabilizer in the actual quotient frame action. -/
theorem eisensteinLocalProjectiveEmbedding_range :
    eisensteinLocalProjectiveEmbedding.range =
      MulAction.stabilizer EisensteinProjectiveModel eisensteinStandardFrame := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨q, rfl⟩ := eisensteinFrameModuloScalarsEquiv.surjective h
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective eisensteinFrameScalarSubgroup q
    change eisensteinLocalProjectiveEmbedding (eisensteinFrameModuloScalarsEquiv
      (QuotientGroup.mk n)) ∈ MulAction.stabilizer EisensteinProjectiveModel eisensteinStandardFrame
    rw [eisensteinLocalProjectiveEmbedding_mk]
    change (QuotientGroup.mk (eisensteinCentralizerEquiv n.val) : EisensteinProjectiveModel) •
      eisensteinStandardFrame = eisensteinStandardFrame
    rw [eisensteinProjectiveFrameAction_mk]
    change n.val ∈ MulAction.stabilizer eisensteinHermitianGroup eisensteinStandardFrame
    rw [eisensteinStandardFrame_stabilizer]
    exact n.property
  · intro hg
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective eisensteinCentralizerScalars g
    obtain ⟨f, rfl⟩ := eisensteinCentralizerEquiv.surjective c
    have hf : f ∈ eisensteinCoordinateFrameStabilizer := by
      rw [← eisensteinStandardFrame_stabilizer]
      change f • eisensteinStandardFrame = eisensteinStandardFrame
      change (QuotientGroup.mk (eisensteinCentralizerEquiv f) : EisensteinProjectiveModel) •
        eisensteinStandardFrame = eisensteinStandardFrame at hg
      rwa [eisensteinProjectiveFrameAction_mk] at hg
    exact ⟨eisensteinFrameModuloScalarsEquiv (QuotientGroup.mk (⟨f,hf⟩ :
      eisensteinCoordinateFrameStabilizer)), eisensteinLocalProjectiveEmbedding_mk _⟩

end Atlas.Conway

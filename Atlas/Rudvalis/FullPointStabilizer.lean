import Atlas.Rudvalis.FullCoupleStabilizer
import Atlas.Rudvalis.LocalTransitivity

namespace Atlas.Rudvalis

theorem coupleFusionGroup_le_localFusionGroup : coupleFusionGroup≤localFusionGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨a,rfl⟩|rfl)
  · exact codeReferenceGaussianHom_mem ⟨a.val,a.prop.1⟩
  · exact localFusionT_mem_localFusionGroup

/-- The explicitly generated orthogonal-shell group is the full Gaussian point stabilizer. -/
theorem localFusionGroup_eq_point_stabilizer :
    localFusionGroup=MulAction.stabilizer gaussianLatticeGroup localReferenceCross := by
  apply le_antisymm localFusionGroup_le_stabilizer
  intro g hg
  change g • localReferenceCross=localReferenceCross at hg
  have hgy : CrossOrthogonal localReferenceCross (g • referenceSecondCross) := by
    have h := (crossOrthogonal_gaussian g localReferenceCross referenceSecondCross).mpr
      reference_crosses_orthogonal
    rwa [hg] at h
  have ha : g • referenceSecondCross∈MulAction.orbit localFusionGroup localThirdCross := by
    rw [localFusionGroup_orthogonal_orbit]
    exact hgy
  have hb : referenceSecondCross∈MulAction.orbit localFusionGroup localThirdCross := by
    rw [localFusionGroup_orthogonal_orbit]
    exact reference_crosses_orthogonal
  obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp ha
  obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hb
  let k : localFusionGroup := a*b⁻¹
  have hk : k.val • referenceSecondCross=g • referenceSecondCross := by
    change (a*b⁻¹) • referenceSecondCross=g • referenceSecondCross
    rw [mul_smul,←hb,inv_smul_smul,ha]
    exact congrArg (fun z : MinimalCross => g • z) hb.symm
  have hkx : k.val • localReferenceCross=localReferenceCross := localFusionGroup_fix k
  have hm : k.val⁻¹*g∈coupleFusionGroup := by
    rw [coupleFusionGroup_eq_pair_stabilizer]
    constructor
    · change (k.val⁻¹*g) • localReferenceCross=localReferenceCross
      rw [mul_smul,hg,←hkx,inv_smul_smul]
      exact hkx.symm
    · change (k.val⁻¹*g) • referenceSecondCross=referenceSecondCross
      rw [mul_smul,←hk,inv_smul_smul]
  have h := localFusionGroup.mul_mem k.prop (coupleFusionGroup_le_localFusionGroup hm)
  simpa only [mul_inv_cancel_left] using h

end Atlas.Rudvalis

import Atlas.Tits.LocalGeneration
import Atlas.Tits.MonomialNormalClosure

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384

/-- The intermediate column already present in the inherited fusion certificate. -/
theorem fusion_middle_reference_column :
    localFusionVector 4 0 = (-16 : ℚ) • originalFrame (0,1) := by
  unfold localFusionVector seedIntegerRational originalFrame
  rw [← map_smul]
  congr 1
  funext j
  have h : localFusionNumerator 4 0 j = if j=(0,1) then -32 else 0 := by
    decide +kernel +revert
  simp only [h, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> norm_num

/-- The inherited g=SUS fixes the first cross, with scalar -1 on its representative. -/
theorem localFusionG_reference_vector :
    localFusionG.val (originalFrame (0,1)) = -originalFrame (0,1) := by
  have hs1 : frameComparison (localFusionVector 1 0) =
      (1/4:ℚ) • localFusionVector 2 0 := by simpa using localFusionVector_S 0 0
  have hs3 : frameComparison (localFusionVector 3 0) =
      (1/4:ℚ) • localFusionVector 4 0 := by simpa using localFusionVector_S 1 0
  have hu : rationalMonomialHom codeU.val (localFusionVector 2 0) =
      localFusionVector 3 0 := by simpa using localFusionVector_U 0 0
  have hstart : localFusionVector 1 0 = originalFrame (0,1) := by
    rw [show localFusionVector 1 0 = localFusionVector 0 0 from rfl,localFusionVector_zero]
    rfl
  have hc (g : codeGroup) (v : RationalSpace) :
      (codeGaussianHom g).val v=rationalMonomialHom g.val v := rfl
  simp only [localFusionG,Subgroup.coe_mul,LinearEquiv.mul_apply,gaussianFrameExchange_val,hc]
  rw [hstart] at hs1
  rw [hs1,map_smul,hu,map_smul,hs3,smul_smul,fusion_middle_reference_column,smul_smul]
  norm_num

theorem localFusionG_fixes_reference :
    localFusionG • localReferenceCross = localReferenceCross := by
  apply gaussian_coordinateCross_of_negative
  rw [← localFusionSource_axis]
  exact localFusionG_reference_vector

noncomputable def localG : Ambient :=
  ⟨QuotientGroup.mk localFusionG,localFusionG_fixes_reference⟩

theorem fusionW_fixes_reference : codeW ∈ codeReferenceStabilizer := by
  apply original_coordinate_cross_fix codeW seedWMonomial codeW_transport
  decide +kernel

/-- The concrete t word is inherited without changing the projective model. -/
theorem localT_eq_g_word :
    localT = localG * codePointHom ⟨codeV,localCodeV_fixes_reference⟩ *
      localG * codePointHom ⟨codeW,fusionW_fixes_reference⟩ := by
  apply Subtype.ext
  rfl

theorem ambient_generated_by_monomial_g :
    monomialPointGroup ⊔ Subgroup.zpowers localG = ⊤ := by
  apply top_unique
  rw [← ambient_generated_by_monomial_t]
  apply sup_le le_sup_left
  apply Subgroup.zpowers_le.mpr
  rw [localT_eq_g_word]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left ⟨_,rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_left ⟨_,rfl⟩

end Atlas.Tits

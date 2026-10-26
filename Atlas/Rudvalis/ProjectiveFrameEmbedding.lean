import Atlas.Rudvalis.ProjectiveCrossFaithful

namespace Atlas.Rudvalis

noncomputable def codeProjectiveHom : codeGroup →* RudvalisGroup :=
  (QuotientGroup.mk' gaussianScalarSubgroup).comp codeGaussianHom

theorem codeProjectiveHom_kernel : codeProjectiveHom.ker=GaussianUnits := by
  ext g
  change (QuotientGroup.mk (codeGaussianHom g) : RudvalisGroup)=1 ↔ g∈GaussianUnits
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨u,hu,he⟩
    exact codeGaussianHom_injective he ▸ hu
  · intro hg
    exact ⟨g,hg,rfl⟩

noncomputable def projectiveCodeHom : ProjectiveCodeGroup →* RudvalisGroup :=
  QuotientGroup.lift GaussianUnits codeProjectiveHom codeProjectiveHom_kernel.symm.le

theorem projectiveCodeHom_injective : Function.Injective projectiveCodeHom :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr codeProjectiveHom_kernel.symm

noncomputable def projectiveFrameGroup : Subgroup RudvalisGroup := projectiveCodeHom.range

noncomputable def projectiveFrameEquiv : ProjectiveCodeGroup ≃* projectiveFrameGroup :=
  MonoidHom.ofInjective projectiveCodeHom_injective

theorem projectiveFrameGroup_order : Nat.card projectiveFrameGroup=344064 := by
  rw [←Nat.card_congr projectiveFrameEquiv.toEquiv,projectiveCodeGroup_order]

set_option maxRecDepth 4096 in
theorem projectiveFrameGroup_index : projectiveFrameGroup.index=424125 := by
  have h := projectiveFrameGroup.index_mul_card
  rw [projectiveFrameGroup_order,rudvalisGroup_order] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0<344064) h

noncomputable def projectiveReflection : RudvalisGroup := QuotientGroup.mk rudvalisReflection

theorem projectiveReflection_square : projectiveReflection^2=1 := by
  change (QuotientGroup.mk' gaussianScalarSubgroup) rudvalisReflection^2=1
  rw [←map_pow,←rudvalisReflection_order,pow_orderOf_eq_one,map_one]

theorem projectiveFrameGroup_reflection_generate :
    projectiveFrameGroup ⊔ Subgroup.zpowers projectiveReflection=⊤ := by
  apply top_unique
  intro q _
  induction q using QuotientGroup.induction_on with
  | H g =>
    refine generatedGaussianGroup_induction
      (P := fun a=> (QuotientGroup.mk a : RudvalisGroup)∈projectiveFrameGroup ⊔ Subgroup.zpowers projectiveReflection)
      ?_ ?_ ?_ ?_ ?_ g (full_gaussian_mem_generated g)
    · intro k
      apply Subgroup.mem_sup_left
      exact ⟨QuotientGroup.mk k,rfl⟩
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.one_mem _
    · intro a b ha hb
      exact Subgroup.mul_mem _ ha hb
    · intro a ha
      exact Subgroup.inv_mem _ ha

theorem projectiveFrameGroup_mem_iff (q : RudvalisGroup) :
    q∈projectiveFrameGroup ↔ ∀c,c∈coordinateFrame ↔ q • c∈coordinateFrame := by
  constructor
  · rintro ⟨k,rfl⟩
    induction k using QuotientGroup.induction_on with
    | H k =>
      change ∀c,c∈coordinateFrame ↔ codeGaussianHom k • c∈coordinateFrame
      exact (gaussian_frame_stabilizer _).mpr ⟨k,rfl⟩
  · induction q using QuotientGroup.induction_on with
    | H g =>
      intro hg
      obtain ⟨k,hk⟩ := (gaussian_frame_stabilizer g).mp hg
      refine ⟨QuotientGroup.mk k,?_⟩
      change (QuotientGroup.mk (codeGaussianHom k) : RudvalisGroup)=QuotientGroup.mk g
      rw [hk]

theorem projectiveFrameGroup_index_odd : Odd projectiveFrameGroup.index := by
  rw [projectiveFrameGroup_index]
  exact ⟨212062,rfl⟩

theorem rudvalisGroup_nontrivial : Nontrivial RudvalisGroup :=
  Finite.one_lt_card_iff_nontrivial.mp (by rw [rudvalisGroup_order]; decide)

end Atlas.Rudvalis


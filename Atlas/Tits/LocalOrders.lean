import Atlas.Tits.LocalSuborbits

namespace Atlas.Tits
open Atlas.Rudvalis

theorem codeGaussian_scalar_iff (g : codeGroup) :
    codeGaussianHom g∈gaussianScalarSubgroup ↔ g∈GaussianUnits := by
  constructor
  · rintro ⟨u,hu,he⟩
    exact codeGaussianHom_injective he ▸ hu
  · intro h; exact ⟨g,h,rfl⟩

theorem codePointHom_kernel (g : codeReferenceStabilizer) :
    g∈codePointHom.ker ↔ g.val∈GaussianUnits := by
  change codePointHom g=1 ↔ _
  rw [Subtype.ext_iff]
  change (QuotientGroup.mk (codeGaussianHom g.val) : RudvalisGroup)=1 ↔ _
  rw [QuotientGroup.eq_one_iff,codeGaussian_scalar_iff]

noncomputable def codePointKernelEquiv : codePointHom.ker ≃* GaussianUnits where
  toFun g := ⟨g.val.val,(codePointHom_kernel g.val).mp g.prop⟩
  invFun u := ⟨⟨u.val,gaussianUnits_cross_fix u localReferenceCross⟩,
    (codePointHom_kernel _).mpr u.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem cardMonomialPointGroup : Nat.card monomialPointGroup=12288 := by
  have h := codePointHom.ker.card_mul_index
  rw [Subgroup.index_ker, Nat.card_congr codePointKernelEquiv.toEquiv,gaussianUnits_card] at h
  have hc : Nat.card codeReferenceStabilizer=49152 :=
    coordinateCross_stabilizer_order _ (coordinateCross_mem _)
  rw [hc] at h
  change Nat.card monomialPointGroup=12288
  change 4*Nat.card monomialPointGroup=49152 at h
  omega

noncomputable def codePairHom : codeCoupleStabilizer →* pairStabilizer where
  toFun g := ⟨codePointHom ⟨g.val,g.prop.1⟩,Subtype.ext (by
    change codeGaussianHom g.val • referenceSecondCross=referenceSecondCross
    rw [codeGaussianHom_cross];exact g.prop.2)⟩
  map_one' := Subtype.ext (Subtype.ext (map_one ((QuotientGroup.mk' gaussianScalarSubgroup).comp
    (codeGaussianHom.comp codeCoupleStabilizer.subtype))))
  map_mul' g h := Subtype.ext (Subtype.ext (map_mul ((QuotientGroup.mk' gaussianScalarSubgroup).comp
    (codeGaussianHom.comp codeCoupleStabilizer.subtype)) g h))

noncomputable def monomialPairGroup : Subgroup pairStabilizer := codePairHom.range

theorem codePairHom_kernel (g : codeCoupleStabilizer) :
    g∈codePairHom.ker ↔ g.val∈GaussianUnits := by
  change codePairHom g=1 ↔ _
  rw [Subtype.ext_iff,Subtype.ext_iff]
  change (QuotientGroup.mk (codeGaussianHom g.val) : RudvalisGroup)=1 ↔ _
  rw [QuotientGroup.eq_one_iff,codeGaussian_scalar_iff]

noncomputable def codePairKernelEquiv : codePairHom.ker ≃* GaussianUnits where
  toFun g := ⟨g.val.val,(codePairHom_kernel g.val).mp g.prop⟩
  invFun u := ⟨⟨u.val,gaussianUnits_cross_fix u localReferenceCross,
    gaussianUnits_cross_fix u referenceSecondCross⟩,(codePairHom_kernel _).mpr u.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem cardMonomialPairGroup : Nat.card monomialPairGroup=4096 := by
  have h := codePairHom.ker.card_mul_index
  rw [Subgroup.index_ker, Nat.card_congr codePairKernelEquiv.toEquiv,gaussianUnits_card,
    codeCoupleStabilizer_order] at h
  change 4*Nat.card monomialPairGroup=16384 at h
  omega

theorem indexMonomialPairGroup : monomialPairGroup.index=5 := by
  have h := monomialPairGroup.card_mul_index
  rw [cardMonomialPairGroup,cardPairStabilizer] at h
  omega

/-- Noncommutativity is established before any transfer or derived simplicity theorem. -/
theorem ambient_nonabelian : ¬IsMulCommutative Ambient := by
  intro hc
  have hcomm := isMulCommutative_iff.mp hc
  have hb : pairStabilizer=⊥ := by
    apply pairStabilizer.eq_bot_iff_forall.mpr
    intro g hg
    apply faithfulSMul_iff.mp (inferInstance : FaithfulSMul Ambient Neighbours) g
    intro c
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq Ambient referenceNeighbour c
    change g • c=c
    rw [←ha,←mul_smul,hcomm g a,mul_smul]
    exact congrArg (fun z : Neighbours => a • z) hg
  have h := cardPairStabilizer
  rw [hb] at h
  norm_num at h

end Atlas.Tits

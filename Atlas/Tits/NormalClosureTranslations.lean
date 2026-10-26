import Atlas.Tits.LocalRowMatrix

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
set_option maxRecDepth 16384

noncomputable def codePointToMonomial : codeReferenceStabilizer →* monomialPointGroup :=
  codePointHom.rangeRestrict

noncomputable def pointNormalPreimage : Subgroup codeReferenceStabilizer :=
  monomialNormalClosure.comap codePointToMonomial
noncomputable def codeNormalImage : Subgroup codeGroup :=
  pointNormalPreimage.map codeReferenceStabilizer.subtype

theorem scalars_le_codeNormalImage : GaussianUnits ≤ codeNormalImage := by
  intro u hu
  let a : codeReferenceStabilizer := ⟨u, gaussianUnits_cross_fix ⟨u,hu⟩ localReferenceCross⟩
  refine ⟨a, ?_, rfl⟩
  have he : codePointToMonomial a = 1 := Subtype.ext ((codePointHom_kernel a).mpr hu)
  change codePointToMonomial a ∈ monomialNormalClosure
  rw [he]
  exact monomialNormalClosure.one_mem

theorem identity_mem_localTranslationPreimage :
    (1 : BinaryMatrix) ∈ translationPreimage codeNormalImage :=
  ⟨codeI, scalars_le_codeNormalImage (Subgroup.mem_zpowers _), codeI_translation_identity⟩

theorem seedRMonomial_square : seedRMonomial ^ 2 = 1 := by
  ext z
  all_goals decide +kernel +revert

theorem localCodeR_square : codeR ^ 2 = 1 := by
  apply Subtype.ext
  change (seedConjugateHom seedRMonomial) ^ 2 = 1
  rw [← map_pow, seedRMonomial_square, map_one]

noncomputable def pointR : codeReferenceStabilizer := ⟨codeR, coupleCodeR_mem.1⟩
noncomputable def pointD : codeReferenceStabilizer := ⟨coupleCodeD, localCodeD_fixes_reference⟩
noncomputable def monomialR : monomialPointGroup := codePointToMonomial pointR
noncomputable def monomialUWord : monomialPointGroup := (monomialN * monomialR) ^ 4

theorem monomialR_square : monomialR ^ 2 = 1 := by
  rw [monomialR, ← map_pow]
  have h : pointR ^ 2 = 1 := Subtype.ext localCodeR_square
  rw [h, map_one]

theorem monomialUWord_mem_normalClosure : monomialUWord ∈ monomialNormalClosure := by
  letI : monomialNormalClosure.Normal := Subgroup.normalClosure_normal
  apply (QuotientGroup.eq_one_iff _).mp
  let f := QuotientGroup.mk' monomialNormalClosure
  have hn : f monomialN = 1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Set.mem_singleton _))
  change f ((monomialN * monomialR) ^ 4) = 1
  rw [map_pow, map_mul, hn, one_mul, show 4 = 2 * 2 by decide, pow_mul,
    ← map_pow, monomialR_square, map_one, one_pow]

theorem localCodeUWord_mem_codeNormalImage : localCodeUWord ∈ codeNormalImage := by
  let a : codeReferenceStabilizer := (pointD ^ 4 * pointR) ^ 4
  refine ⟨a, ?_, rfl⟩
  change codePointToMonomial a ∈ monomialNormalClosure
  have he : codePointToMonomial a = monomialUWord := by
    simp only [a, map_pow, map_mul]
    rfl
  rw [he]
  exact monomialUWord_mem_normalClosure

theorem uMatrix_mem_localTranslationPreimage :
    uTranslationMatrix ∈ translationPreimage codeNormalImage :=
  ⟨localCodeUWord, localCodeUWord_mem_codeNormalImage, localCodeUWord_translation⟩

end Atlas.Tits

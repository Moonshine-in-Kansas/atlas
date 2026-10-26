import Atlas.Tits.LocalRowNormalClosure
import Atlas.Tits.LocalTranslationVanishing

/-! The actual monomial point-stabilizer quotient by the normal closure of d⁴.
Its two possible bits are represented by the inherited q and R. -/

namespace Atlas.Tits
open Atlas.Rudvalis

instance monomialNormalClosure_normal : monomialNormalClosure.Normal :=
  Subgroup.normalClosure_normal
instance pointNormalPreimage_normal : pointNormalPreimage.Normal :=
  (inferInstance : monomialNormalClosure.Normal).comap codePointToMonomial

noncomputable def pointQ : codeReferenceStabilizer :=
  ⟨localCodeQ,localCodeQ_fixes_reference⟩
noncomputable def monomialQ : monomialPointGroup := codePointToMonomial pointQ

noncomputable abbrev MonomialSmallQuotient := monomialPointGroup ⧸ monomialNormalClosure
noncomputable def monomialSmallMap : codeReferenceStabilizer →* MonomialSmallQuotient :=
  (QuotientGroup.mk' monomialNormalClosure).comp codePointToMonomial
noncomputable def monomialSmallQ : MonomialSmallQuotient := monomialSmallMap pointQ
noncomputable def monomialSmallR : MonomialSmallQuotient := monomialSmallMap pointR

noncomputable def localRowNormalImage : Subgroup localRowStabilizer :=
  pointNormalPreimage.map codeReferenceRowHom
instance localRowNormalImage_normal : localRowNormalImage.Normal :=
  Subgroup.Normal.map inferInstance codeReferenceRowHom codeReferenceRowHom_surjective

theorem localRowN_mem_normalImage : localRowN ∈ localRowNormalImage := by
  refine ⟨pointD^4,?_,?_⟩
  · change codePointToMonomial (pointD^4) ∈ monomialNormalClosure
    rw [map_pow]
    change monomialN ∈ monomialNormalClosure
    exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  · exact Subtype.ext localRowN_actual.symm

theorem codeReferenceRowHom_pointR : codeReferenceRowHom pointR = localRowR :=
  Subtype.ext localRowR_actual.symm

theorem monomialSmallMap_eq_one (g : codeReferenceStabilizer)
    (hg : g ∈ pointNormalPreimage) : monomialSmallMap g = 1 :=
  (QuotientGroup.eq_one_iff _).mpr hg

/-- Inside the row kernel, the trace-zero subgroup kills every element except
for the possible bit represented by the actual q. -/
theorem monomialSmallMap_row_kernel (g : codeReferenceStabilizer)
    (hg : codeReferenceRowHom g = 1) :
    monomialSmallMap g = 1 ∨ monomialSmallMap g = monomialSmallQ := by
  have hk : g.val ∈ codeRowKernel := congrArg Subtype.val hg
  let k : codeRowKernel := ⟨g.val,hk⟩
  let M : pointMatrixSpace :=
    ⟨(codeRowMatrixHom k).toAdd,(rowMatrix_fixes_reference_iff k).mp g.prop⟩
  let Q : pointMatrixSpace := ⟨qTranslationMatrix,local_translation_point_constraints.1⟩
  have hQ : pointTrace Q = 1 := local_translation_traces.1
  have hm : pointTrace M = 0 ∨ pointTrace M = 1 := by
    have h : ∀ b : Bit, b = 0 ∨ b = 1 := by decide +kernel
    exact h _
  rcases hm with ht | ht
  · exact Or.inl (monomialSmallMap_eq_one g
      (traceZero_translation_mem_pointNormalPreimage g M ht (rowMatrix_coordinates k)))
  · have htrace : pointTrace (M-Q) = 0 := by rw [map_sub,ht,hQ,sub_self]
    have hperm : codePermutationHom (g*pointQ⁻¹).val =
        coordinateTranslationHom (Multiplicative.ofAdd (M-Q).val) := by
      change codePermutationHom (g.val*localCodeQ⁻¹) = _
      rw [map_mul,map_inv,rowMatrix_coordinates k,localCodeQ_translation,
        ← map_inv,← map_mul]
      congr 1
      change M.val + -Q.val = (M-Q).val
      exact (sub_eq_add_neg M.val Q.val).symm
    have hmem := traceZero_translation_mem_pointNormalPreimage (g*pointQ⁻¹) (M-Q) htrace hperm
    have he := monomialSmallMap_eq_one (g*pointQ⁻¹) hmem
    rw [map_mul,map_inv] at he
    exact Or.inr (mul_inv_eq_one.mp he)

/-- The four displayed representatives come from the two actual filtration
layers; no quotient order is assumed. -/
theorem monomialSmallMap_four_representatives (g : codeReferenceStabilizer) :
    monomialSmallMap g = 1 ∨ monomialSmallMap g = monomialSmallQ ∨
      monomialSmallMap g = monomialSmallR ∨
      monomialSmallMap g = monomialSmallQ * monomialSmallR := by
  obtain ⟨h,hr | hr⟩ := localRow_normal_coset_representatives localRowNormalImage
    localRowN_mem_normalImage (codeReferenceRowHom g)
  · obtain ⟨n,hn,he⟩ := h.prop
    have hrow : codeReferenceRowHom (g*n⁻¹) = 1 := by
      rw [map_mul,map_inv,hr,he,mul_inv_cancel]
    have hsmall : monomialSmallMap (g*n⁻¹) = monomialSmallMap g := by
      rw [map_mul,map_inv,monomialSmallMap_eq_one n hn,inv_one,mul_one]
    rcases monomialSmallMap_row_kernel (g*n⁻¹) hrow with hh | hh
    · exact Or.inl (hsmall.symm.trans hh)
    · exact Or.inr (Or.inl (hsmall.symm.trans hh))
  · obtain ⟨n,hn,he⟩ := h.prop
    have hrow : codeReferenceRowHom (g*n⁻¹*pointR⁻¹) = 1 := by
      rw [map_mul,map_mul,map_inv,map_inv,hr,he,codeReferenceRowHom_pointR,
        mul_inv_cancel_right,mul_inv_cancel]
    have hsmall : monomialSmallMap g =
        monomialSmallMap (g*n⁻¹*pointR⁻¹) * monomialSmallR := by
      rw [map_mul,map_mul,map_inv,map_inv,monomialSmallMap_eq_one n hn,inv_one,mul_one]
      change monomialSmallMap g =
        monomialSmallMap g * monomialSmallR⁻¹ * monomialSmallR
      simp only [mul_assoc,inv_mul_cancel,mul_one]
    rcases monomialSmallMap_row_kernel (g*n⁻¹*pointR⁻¹) hrow with hh | hh
    · exact Or.inr (Or.inr (Or.inl (by rw [hsmall,hh,one_mul])))
    · exact Or.inr (Or.inr (Or.inr (by rw [hsmall,hh])))

theorem monomialSmallMap_surjective : Function.Surjective monomialSmallMap :=
  (QuotientGroup.mk'_surjective monomialNormalClosure).comp
    (MonoidHom.rangeRestrict_surjective codePointHom)

theorem monomialSmallQuotient_four_representatives (g : MonomialSmallQuotient) :
    g = 1 ∨ g = monomialSmallQ ∨ g = monomialSmallR ∨
      g = monomialSmallQ * monomialSmallR := by
  obtain ⟨g,rfl⟩ := monomialSmallMap_surjective g
  exact monomialSmallMap_four_representatives g

theorem monomialSmallQuotient_card_le_four : Nat.card MonomialSmallQuotient ≤ 4 := by
  let f : Fin 4 → MonomialSmallQuotient :=
    ![1,monomialSmallQ,monomialSmallR,monomialSmallQ*monomialSmallR]
  have hf : Function.Surjective f := by
    intro g
    rcases monomialSmallQuotient_four_representatives g with h | h | h | h
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
    · exact ⟨3,h.symm⟩
  simpa using Nat.card_le_card_of_surjective f hf

theorem monomialNormalClosure_index_le_four : monomialNormalClosure.index ≤ 4 :=
  monomialSmallQuotient_card_le_four

theorem monomialSmallQ_square : monomialSmallQ^2 = 1 := by
  change monomialSmallMap pointQ ^ 2 = 1
  rw [← map_pow]
  exact monomialSmallMap_eq_one _
    ((pointNormalPreimage_iff_image _).mpr localCodeQ_square_mem_codeNormalImage)

theorem monomialSmallR_square : monomialSmallR^2 = 1 := by
  change (QuotientGroup.mk' monomialNormalClosure monomialR)^2 = 1
  rw [← map_pow,monomialR_square,map_one]

theorem monomialSmallQ_commute_R : Commute monomialSmallQ monomialSmallR := by
  change monomialSmallQ*monomialSmallR = monomialSmallR*monomialSmallQ
  rcases monomialSmallQuotient_four_representatives (monomialSmallR*monomialSmallQ) with
    h | h | h | h
  · exact (mul_eq_one_comm.mp h).trans h.symm
  · have hr : monomialSmallR = 1 := mul_right_cancel (h.trans (one_mul _).symm)
    simp [hr]
  · have hq : monomialSmallQ = 1 := mul_left_cancel (h.trans (mul_one _).symm)
    simp [hq]
  · exact h.symm

/-- The quotient has exponent dividing two, including the possible trivial case. -/
theorem monomialSmallQuotient_square (g : MonomialSmallQuotient) : g^2 = 1 := by
  rcases monomialSmallQuotient_four_representatives g with h | h | h | h
  · rw [h,one_pow]
  · rw [h,monomialSmallQ_square]
  · rw [h,monomialSmallR_square]
  · rw [h,monomialSmallQ_commute_R.mul_pow,monomialSmallQ_square,monomialSmallR_square,one_mul]

/-- Explicit generation by the inherited elements R and q. -/
theorem monomialSmallQuotient_generated :
    Subgroup.closure ({monomialSmallQ,monomialSmallR} : Set MonomialSmallQuotient) = ⊤ := by
  apply top_unique
  intro g _
  have hq : monomialSmallQ ∈ Subgroup.closure ({monomialSmallQ,monomialSmallR} : Set MonomialSmallQuotient) :=
    Subgroup.subset_closure (by simp)
  have hr : monomialSmallR ∈ Subgroup.closure ({monomialSmallQ,monomialSmallR} : Set MonomialSmallQuotient) :=
    Subgroup.subset_closure (by simp)
  rcases monomialSmallQuotient_four_representatives g with h | h | h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h]; exact hq
  · rw [h]; exact hr
  · rw [h]; exact Subgroup.mul_mem _ hq hr

end Atlas.Tits

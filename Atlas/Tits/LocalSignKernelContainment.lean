import Atlas.Tits.NormalClosureTranslations
import Atlas.Rudvalis.FrameSignCommutators

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
open scoped BigOperators commutatorElement
set_option maxRecDepth 16384

/-- The normal closure contains its actual order-three generator before quotienting. -/
theorem localCodeN_mem_codeNormalImage : coupleCodeD^4∈codeNormalImage := by
  refine ⟨pointD^4,?_,rfl⟩
  change codePointToMonomial (pointD^4)∈monomialNormalClosure
  have he : codePointToMonomial (pointD^4)=monomialN := by
    rw [map_pow]
    rfl
  rw [he]
  exact Subgroup.subset_normalClosure (Set.mem_singleton _)

theorem codeNormalImage_commutator (a b : codeGroup)
    (ha : a∈codeNormalImage) (hb : b∈codeReferenceStabilizer) :
    ⁅a,b⁆∈codeNormalImage := by
  let : monomialNormalClosure.Normal := Subgroup.normalClosure_normal
  let : pointNormalPreimage.Normal :=
    (inferInstance : monomialNormalClosure.Normal).comap codePointToMonomial
  obtain ⟨u,hu,rfl⟩ := ha
  let v : codeReferenceStabilizer := ⟨b,hb⟩
  have hc : ⁅u,v⁆∈pointNormalPreimage :=
    Subgroup.commutator_le_left pointNormalPreimage ⊤
      (Subgroup.commutator_mem_commutator hu (Subgroup.mem_top _))
  exact ⟨⁅u,v⁆,hc,map_commutatorElement codeReferenceStabilizer.subtype _ _⟩

theorem seedARowSign_mem_point (v : E) : seedARowSign v∈codeReferenceStabilizer := by
  change seedARowSign v • localReferenceCross=localReferenceCross
  rw [localReferenceCross_eq,coordinateCross_action]
  rfl

set_option maxHeartbeats 4000000 in
theorem original_N_sign_one_commutator :
    ⁅coupleOriginalD^4,seedOriginalRowSign (binaryLabel 1)⁆=
      seedOriginalRowSign (binaryLabel 7) := by
  ext z
  all_goals decide +kernel +revert

set_option maxHeartbeats 4000000 in
theorem original_N_sign_two_commutator :
    ⁅coupleOriginalD^4,seedOriginalRowSign (binaryLabel 2)⁆=
      seedOriginalRowSign (binaryLabel 1) := by
  ext z
  all_goals decide +kernel +revert

theorem code_N_sign_commutator_of_original (v w : E)
    (h : ⁅coupleOriginalD^4,seedOriginalRowSign v⁆=seedOriginalRowSign w) :
    ⁅coupleCodeD^4,seedARowSign v⁆=seedARowSign w := by
  apply Subtype.ext
  change ⁅coupleCodeD.val^4,(seedARowSign v).val⁆=(seedARowSign w).val
  rw [coupleCodeD_transport,seedARowSign_conjugate,seedARowSign_conjugate,
    ←map_pow,←map_commutatorElement,h]

theorem linear_sign_one_mem_codeNormalImage : seedARowSign (binaryLabel 1)∈codeNormalImage := by
  rw [←code_N_sign_commutator_of_original _ _ original_N_sign_two_commutator]
  exact codeNormalImage_commutator _ _ localCodeN_mem_codeNormalImage (seedARowSign_mem_point _)

theorem linear_sign_seven_mem_codeNormalImage : seedARowSign (binaryLabel 7)∈codeNormalImage := by
  rw [←code_N_sign_commutator_of_original _ _ original_N_sign_one_commutator]
  exact codeNormalImage_commutator _ _ localCodeN_mem_codeNormalImage (seedARowSign_mem_point _)

theorem linear_sign_four_mem_codeNormalImage : seedARowSign (binaryLabel 4)∈codeNormalImage := by
  have hi : codeI^2∈codeNormalImage :=
    codeNormalImage.pow_mem (scalars_le_codeNormalImage (Subgroup.mem_zpowers _)) 2
  have hh := codeNormalImage_commutator _ _
    (codeNormalImage_commutator _ _ localCodeN_mem_codeNormalImage localCodeV_fixes_reference)
    localCodeV_fixes_reference
  rw [code_double_commutator_sign] at hh
  have h := codeNormalImage.mul_mem (codeNormalImage.inv_mem hi) hh
  simpa only [inv_mul_cancel_left] using h

theorem local_hammingSigns_contained : hammingSignCode≤rowSignPreimage codeNormalImage := by
  let W := rowSignPreimage codeNormalImage
  have hscalar : (fun _=>1 : Point→Bit)∈W := by
    exact ⟨codeI^2,codeNormalImage.pow_mem
      (scalars_le_codeNormalImage (Subgroup.mem_zpowers _)) 2,codeI_square_rowSign⟩
  have lift (v : E) (hv : seedARowSign v∈codeNormalImage) : affineRowSign 0 v∈W := by
    refine ⟨seedARowSign v,hv,?_⟩
    change SemidirectProduct.inl (Multiplicative.ofAdd (rowSigns (fun p=>dot v p.val)))=
      rowSignHom (Multiplicative.ofAdd (affineRowSign 0 v))
    have he : affineRowSign 0 v=(fun p=>dot v p.val) := by funext p;exact zero_add _
    rw [he]
    rfl
  have h1 := lift _ linear_sign_one_mem_codeNormalImage
  have h4 := lift _ linear_sign_four_mem_codeNormalImage
  have h7 := lift _ linear_sign_seven_mem_codeNormalImage
  have hb (i : Fin 3) : affineRowSign 0 (basisPoint i).val∈W := by
    fin_cases i
    · exact h1
    · have he : affineRowSign 0 (basisPoint 1).val=
          affineRowSign 0 (binaryLabel 1)+affineRowSign 0 (binaryLabel 4)+affineRowSign 0 (binaryLabel 7) := by
        decide +kernel
      change affineRowSign 0 (basisPoint 1).val∈W
      rw [he]
      exact W.add_mem (W.add_mem h1 h4) h7
    · exact h4
  have hv (v : E) : affineRowSign 0 v∈W := by
    rw [affineRowSign_linear_expansion]
    exact W.sum_mem (fun i _=>W.smul_mem _ (hb i))
  intro s hs
  obtain ⟨⟨a,v⟩,he⟩ := affineRowSign_surjective ⟨s,hs⟩
  have he' : affineRowSign a v=s := congrArg Subtype.val he
  rw [←he']
  have heq : affineRowSign a v=a • (fun _=>1 : Point→Bit)+affineRowSign 0 v := by
    funext p;simp [affineRowSign]
  rw [heq]
  exact W.add_mem (W.smul_mem a hscalar) (hv v)

/-- The entire actual sixteen-element sign kernel lies in the local normal closure. -/
theorem signKernel_le_codeNormalImage : codePermutationHom.ker≤codeNormalImage := by
  intro g hg
  let s : signPatterns := (codeSignKernelEquiv ⟨g,hg⟩).toAdd
  let a := hammingSignEquiv.symm s
  have ha := rowSignCode_mem_of_hammingSigns codeNormalImage local_hammingSigns_contained a
  have he : rowSignCode a=g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact congrArg Subtype.val (hammingSignEquiv.apply_symm_apply s)
    · exact ((codePermutationHom_kernel g).mp hg).symm
  exact he ▸ ha

end Atlas.Tits

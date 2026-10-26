import Atlas.Rudvalis.ProjectiveFrameFiltration
import Mathlib.LinearAlgebra.Quotient.Defs

set_option maxRecDepth 2048

namespace Atlas.Rudvalis

noncomputable def projectiveRowProjection : codeRowKernel →* projectiveRowKernel where
  toFun g := ⟨QuotientGroup.mk' GaussianUnits g.val,g.prop⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul (QuotientGroup.mk' GaussianUnits) g.val h.val)

theorem projectiveRowProjection_surjective : Function.Surjective projectiveRowProjection := by
  intro a
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective GaussianUnits a.val
  have hp : g∈codeRowKernel := by
    change projectiveCodeBlockHom (QuotientGroup.mk' GaussianUnits g)=1
    rw [hg]
    exact a.prop
  exact ⟨⟨g,hp⟩,Subtype.ext hg⟩

theorem projectiveRowProjection_kernel (g : codeRowKernel) :
    g∈projectiveRowProjection.ker ↔ g.val∈GaussianUnits := by
  change projectiveRowProjection g=1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff g.val

noncomputable def matrixScalarLine : Submodule Bit BinaryMatrix :=
  Submodule.span Bit {(1 : BinaryMatrix)}

noncomputable abbrev ProjectiveTranslationModule := BinaryMatrix ⧸ matrixScalarLine

noncomputable def rowMatrixQuotientHom :
    codeRowKernel →* Multiplicative ProjectiveTranslationModule :=
  matrixScalarLine.mkQ.toAddMonoidHom.toMultiplicative.comp codeRowMatrixHom

noncomputable def rowGaussianI : codeRowKernel := ⟨codeI,codeI_blockLinear⟩

theorem rowGaussianI_matrix : codeRowMatrixHom rowGaussianI=Multiplicative.ofAdd 1 := by
  apply binaryTranslationEquiv.injective
  change binaryTranslationEquiv (binaryTranslationEquiv.symm (codeRowTranslationHom rowGaussianI))=_
  rw [binaryTranslationEquiv.apply_symm_apply]
  apply Subtype.ext
  exact codeI_translation_identity

theorem rowGaussianI_matrixQuotient : rowMatrixQuotientHom rowGaussianI=1 := by
  change Multiplicative.ofAdd (matrixScalarLine.mkQ (codeRowMatrixHom rowGaussianI).toAdd)=1
  rw [rowGaussianI_matrix]
  change matrixScalarLine.mkQ (1 : BinaryMatrix)=0
  exact (Submodule.Quotient.mk_eq_zero matrixScalarLine).mpr (Submodule.subset_span (Set.mem_singleton 1))

theorem rowMatrixQuotientHom_kills_scalars :
    projectiveRowProjection.ker ≤ rowMatrixQuotientHom.ker := by
  intro g hg
  obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp ((projectiveRowProjection_kernel g).mp hg)
  have he : g=rowGaussianI^k := Subtype.ext hk.symm
  change rowMatrixQuotientHom g=1
  rw [he,map_zpow,rowGaussianI_matrixQuotient,one_zpow]

noncomputable def projectiveRowMatrixHom :
    projectiveRowKernel →* Multiplicative ProjectiveTranslationModule :=
  (QuotientGroup.lift projectiveRowProjection.ker rowMatrixQuotientHom
    rowMatrixQuotientHom_kills_scalars).comp
    (QuotientGroup.quotientKerEquivOfSurjective projectiveRowProjection
      projectiveRowProjection_surjective).symm.toMonoidHom

theorem projectiveRowMatrixHom_projection (g : codeRowKernel) :
    projectiveRowMatrixHom (projectiveRowProjection g)=rowMatrixQuotientHom g := by
  change QuotientGroup.lift projectiveRowProjection.ker rowMatrixQuotientHom rowMatrixQuotientHom_kills_scalars
    ((QuotientGroup.quotientKerEquivOfSurjective projectiveRowProjection projectiveRowProjection_surjective).symm (projectiveRowProjection g))=_
  rw [show (QuotientGroup.quotientKerEquivOfSurjective projectiveRowProjection
    projectiveRowProjection_surjective).symm (projectiveRowProjection g)=
    QuotientGroup.mk' projectiveRowProjection.ker g from
    (QuotientGroup.quotientKerEquivOfSurjective _ _).symm_apply_apply
      (QuotientGroup.mk' projectiveRowProjection.ker g)]
  rfl

theorem rowMatrixQuotientHom_surjective : Function.Surjective rowMatrixQuotientHom := by
  intro a
  obtain ⟨M,hM⟩ := matrixScalarLine.mkQ_surjective a.toAdd
  obtain ⟨g,hg⟩ := codeRowMatrixHom_surjective (Multiplicative.ofAdd M)
  refine ⟨g,?_⟩
  change Multiplicative.ofAdd (matrixScalarLine.mkQ (codeRowMatrixHom g).toAdd)=a
  rw [hg]
  change Multiplicative.ofAdd (matrixScalarLine.mkQ M)=a
  rw [hM]
  rfl

theorem projectiveRowMatrixHom_surjective : Function.Surjective projectiveRowMatrixHom := by
  intro a
  obtain ⟨g,hg⟩ := rowMatrixQuotientHom_surjective a
  exact ⟨projectiveRowProjection g,(projectiveRowMatrixHom_projection g).trans hg⟩

theorem matrixScalarLine_finrank : Module.finrank Bit matrixScalarLine=1 := by
  apply finrank_span_singleton
  intro h
  have he := congrArg (fun M : BinaryMatrix => M 0 0) h
  simp at he

theorem projectiveTranslationModule_finrank : Module.finrank Bit ProjectiveTranslationModule=8 := by
  have h := matrixScalarLine.finrank_quotient_add_finrank
  rw [matrixScalarLine_finrank] at h
  have hm : Module.finrank Bit BinaryMatrix=9 := by
    simp [BinaryMatrix,Module.finrank_matrix]
  rw [hm] at h
  change Module.finrank Bit ProjectiveTranslationModule+1=9 at h
  omega

theorem projectiveTranslationModule_card : Nat.card ProjectiveTranslationModule=256 := by
  rw [Module.natCard_eq_pow_finrank (K:=Bit),projectiveTranslationModule_finrank]
  norm_num [Bit,Nat.card_eq_fintype_card,ZMod.card]

theorem projectiveRowMatrixHom_kernel_order : Nat.card projectiveRowMatrixHom.ker=8 := by
  have h := projectiveRowMatrixHom.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr projectiveRowMatrixHom_surjective,
    Subgroup.card_top,projectiveCodeBlockHom_kernel_order] at h
  have ht : Nat.card (Multiplicative ProjectiveTranslationModule)=256 := projectiveTranslationModule_card
  rw [ht] at h
  omega

end Atlas.Rudvalis

import Atlas.Rudvalis.FrameTranslationCommutators
import Mathlib.GroupTheory.Nilpotent

namespace Atlas.Rudvalis

theorem codeI_blockLinear : codeBlockLinearHom codeI = 1 := by
  change binaryBlockLinearHom (codePermutationHom codeI)=1
  rw [codeI_translation_identity]
  apply show coordinateTranslationHom (Multiplicative.ofAdd (1 : BinaryMatrix)) ∈ binaryBlockLinearHom.ker from ?_
  rw [binaryBlockLinearHom_kernel_translations]
  exact ⟨_,rfl⟩

theorem gaussianUnits_le_codeRowKernel : GaussianUnits ≤ codeRowKernel :=
  Subgroup.zpowers_le.mpr codeI_blockLinear

noncomputable def projectiveCodeBlockHom : ProjectiveCodeGroup →* (E ≃ₗ[Bit] E) :=
  QuotientGroup.lift GaussianUnits codeBlockLinearHom gaussianUnits_le_codeRowKernel

theorem projectiveCodeBlockHom_mk (g : codeGroup) :
    projectiveCodeBlockHom (QuotientGroup.mk' GaussianUnits g)=codeBlockLinearHom g := rfl

theorem projectiveCodeBlockHom_surjective : Function.Surjective projectiveCodeBlockHom := by
  intro A
  obtain ⟨g,hg⟩ := codeBlockLinearHom_surjective A
  exact ⟨QuotientGroup.mk' GaussianUnits g,hg⟩

noncomputable abbrev projectiveRowKernel := projectiveCodeBlockHom.ker

theorem projectiveCodeBlockHom_kernel_order : Nat.card projectiveCodeBlockHom.ker=2048 := by
  have h := projectiveCodeBlockHom.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr projectiveCodeBlockHom_surjective,
    Nat.card_congr Subgroup.topEquiv.toEquiv,binaryLinearGroup_order,
    projectiveCodeGroup_order] at h
  omega

theorem projectiveCodeBlockHom_kernel_solvable : Group.IsSolvable projectiveCodeBlockHom.ker := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hp : IsPGroup 2 projectiveCodeBlockHom.ker :=
    IsPGroup.of_card (n:=11) (by rw [projectiveCodeBlockHom_kernel_order]; decide)
  have := hp.isNilpotent
  infer_instance

end Atlas.Rudvalis

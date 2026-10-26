import Atlas.Rudvalis.ProjectiveMatrixFiltration
import Mathlib.Algebra.Module.ZMod

namespace Atlas.Rudvalis

noncomputable def rowSignKernelHom : codePermutationHom.ker →* codeRowKernel where
  toFun g := ⟨g.val,by
    change binaryBlockLinearHom (codePermutationHom g.val)=1
    rw [show codePermutationHom g.val=1 from g.prop,map_one]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def projectiveSignHom : codePermutationHom.ker →* projectiveRowKernel :=
  projectiveRowProjection.comp rowSignKernelHom

noncomputable def projectiveSignKernel : Subgroup projectiveRowKernel := projectiveSignHom.range

theorem codeRowMatrixHom_eq_one_iff (g : codeRowKernel) :
    codeRowMatrixHom g=1 ↔ g.val∈codePermutationHom.ker := by
  have h : codeRowMatrixHom g=1 ↔ codeRowTranslationHom g=1 := by
    change binaryTranslationEquiv.symm (codeRowTranslationHom g)=1 ↔ _
    exact map_eq_one_iff binaryTranslationEquiv.symm binaryTranslationEquiv.symm.injective
  exact h.trans (codeRowTranslationHom_kernel g)

theorem projectiveSignKernel_le_matrixKernel : projectiveSignKernel ≤ projectiveRowMatrixHom.ker := by
  rintro _ ⟨g,rfl⟩
  change projectiveRowMatrixHom (projectiveRowProjection (rowSignKernelHom g))=1
  rw [projectiveRowMatrixHom_projection]
  have h : codeRowMatrixHom (rowSignKernelHom g)=1 :=
    (codeRowMatrixHom_eq_one_iff _).mpr g.prop
  change matrixScalarLine.mkQ.toAddMonoidHom.toMultiplicative
    (codeRowMatrixHom (rowSignKernelHom g))=1
  rw [h,map_one]

theorem projectiveRowProjection_scalar_case (g : codeRowKernel)
    (hg : codeRowMatrixHom g=Multiplicative.ofAdd (1 : BinaryMatrix)) :
    projectiveRowProjection g∈projectiveSignKernel := by
  let k := g*rowGaussianI⁻¹
  have hk : codeRowMatrixHom k=1 := by
    dsimp [k]
    rw [map_mul,map_inv,hg,rowGaussianI_matrix,mul_inv_cancel]
  let a : codePermutationHom.ker := ⟨k.val,(codeRowMatrixHom_eq_one_iff k).mp hk⟩
  refine ⟨a,?_⟩
  change projectiveRowProjection k=projectiveRowProjection g
  dsimp [k]
  rw [map_mul,map_inv]
  have hi : projectiveRowProjection rowGaussianI=1 :=
    (projectiveRowProjection_kernel rowGaussianI).mpr (Subgroup.mem_zpowers codeI)
  rw [hi,inv_one,mul_one]

theorem projectiveRowMatrixHom_kernel_eq_signs :
    projectiveRowMatrixHom.ker=projectiveSignKernel := by
  apply le_antisymm _ projectiveSignKernel_le_matrixKernel
  intro a ha
  obtain ⟨g,rfl⟩ := projectiveRowProjection_surjective a
  have hg : rowMatrixQuotientHom g=1 := by
    rw [←projectiveRowMatrixHom_projection]
    exact ha
  have hz : matrixScalarLine.mkQ (codeRowMatrixHom g).toAdd=0 := by
    exact congrArg Multiplicative.toAdd hg
  have hm : (codeRowMatrixHom g).toAdd∈matrixScalarLine :=
    (Submodule.Quotient.mk_eq_zero matrixScalarLine).mp hz
  obtain ⟨b,hb⟩ := (Submodule.mem_span_singleton (R:=Bit)).mp hm
  have cases : b=0 ∨ b=1 := by fin_cases b <;> (first | exact Or.inl rfl | exact Or.inr rfl)
  rcases cases with rfl | rfl
  · have hk : codeRowMatrixHom g=1 := by
      have he : (codeRowMatrixHom g).toAdd=0 := by simpa using hb.symm
      exact congrArg Multiplicative.ofAdd he
    let k : codePermutationHom.ker := ⟨g.val,(codeRowMatrixHom_eq_one_iff g).mp hk⟩
    exact ⟨k,rfl⟩
  · apply projectiveRowProjection_scalar_case
    have he : (codeRowMatrixHom g).toAdd=(1 : BinaryMatrix) := by simpa using hb.symm
    exact congrArg Multiplicative.ofAdd he

theorem projectiveSignKernel_order : Nat.card projectiveSignKernel=8 := by
  rw [←projectiveRowMatrixHom_kernel_eq_signs,projectiveRowMatrixHom_kernel_order]

noncomputable instance projectiveSignKernel_commGroup : CommGroup projectiveSignKernel :=
  { (inferInstance : Group projectiveSignKernel) with
    mul_comm := by
      intro a b
      obtain ⟨x,hx⟩ := a.prop
      obtain ⟨y,hy⟩ := b.prop
      apply Subtype.ext
      change a.val*b.val=b.val*a.val
      rw [←hx,←hy,←map_mul,←map_mul]
      congr 1
      apply codeSignKernelEquiv.injective
      rw [map_mul,map_mul,mul_comm] }

theorem projectiveSignKernel_square (a : projectiveSignKernel) : a^2=1 := by
  obtain ⟨g,hg⟩ := a.prop
  have hsq : g^2=1 := by
    apply codeSignKernelEquiv.injective
    rw [map_pow,map_one,pow_two]
    change Multiplicative.ofAdd ((codeSignKernelEquiv g).toAdd+(codeSignKernelEquiv g).toAdd)=1
    congr 1
    apply Subtype.ext
    funext z
    exact CharTwo.add_self_eq_zero _
  apply Subtype.ext
  change a.val^2=1
  rw [←hg,←map_pow,hsq,map_one]

noncomputable instance projectiveSignKernel_module : Module Bit (Additive projectiveSignKernel) :=
  AddCommGroup.zmodModule (n:=2) (fun a => by
    rw [two_nsmul]
    change Additive.ofMul (a.toMul*a.toMul)=0
    rw [←pow_two]
    rw [projectiveSignKernel_square]
    rfl)

theorem projectiveSignKernel_finrank : Module.finrank Bit (Additive projectiveSignKernel)=3 := by
  have h := Module.natCard_eq_pow_finrank (K:=Bit) (V:=Additive projectiveSignKernel)
  have hc : Nat.card (Additive projectiveSignKernel)=8 := projectiveSignKernel_order
  rw [hc] at h
  have hbit : Nat.card Bit=2 := by simp [Bit,Nat.card_eq_fintype_card,ZMod.card]
  rw [hbit] at h
  exact Nat.pow_right_injective (by decide : 2≤2) (show 2^Module.finrank Bit (Additive projectiveSignKernel)=2^3 from h.symm)

end Atlas.Rudvalis

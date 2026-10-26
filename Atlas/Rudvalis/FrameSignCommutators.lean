import Atlas.Rudvalis.FrameSignConjugation

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped commutatorElement

theorem rowSignHom_commutator (g : codeGroup) (a : Point→Bit) :
    ⁅g.val,rowSignHom (Multiplicative.ofAdd a)⁆=
      rowSignHom (Multiplicative.ofAdd ((a∘codeRowImage g⁻¹)-a)) := by
  rw [commutatorElement_def,rowSignHom_conjugate,←map_inv,←map_mul,sub_eq_add_neg]
  rfl

theorem codeI_square_rowSign : (codeI.val)^2=rowSignHom (Multiplicative.ofAdd (fun _=>1)) := by
  apply monomialHom_injective
  rw [map_pow,pow_two]
  apply LinearEquiv.ext
  intro w
  change monomialHom codeI.val (monomialHom codeI.val w)=_
  rw [codeI_square_action]
  funext z
  change -w z=signedScalar 1 (w z)
  simp [signedScalar]

noncomputable def rowSignPreimage (S : Subgroup codeGroup) : Submodule Bit (Point→Bit) where
  carrier := {a | rowSignHom (Multiplicative.ofAdd a)∈S.map codeGroup.subtype}
  zero_mem' := by
    change rowSignHom 1∈S.map codeGroup.subtype
    rw [map_one]
    exact Subgroup.one_mem _
  add_mem' := by
    intro a b ha hb
    change rowSignHom (Multiplicative.ofAdd a*Multiplicative.ofAdd b)∈S.map codeGroup.subtype
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb
  smul_mem' := by
    intro t a ha
    rcases Atlas.Codes.bit_cases t with rfl|rfl
    · simp only [zero_smul]
      change rowSignHom 1∈S.map codeGroup.subtype
      rw [map_one]
      exact Subgroup.one_mem _
    · simpa only [one_smul] using ha

theorem hammingSigns_mem_commutator_scalars (S : Subgroup codeGroup)
    (hc : commutator codeGroup≤S) (hI : codeI∈S) : hammingSignCode≤rowSignPreimage S := by
  apply hammingSign_differences_scalar_span
  · change rowSignHom (Multiplicative.ofAdd (fun _=>1))∈S.map codeGroup.subtype
    exact ⟨codeI^2,S.pow_mem hI 2,codeI_square_rowSign⟩
  · intro A v
    obtain ⟨g,hg⟩ := codeBlockLinearHom_surjective A⁻¹
    have hr : codeRowImage g⁻¹=linearPointEquiv A := by
      rw [codeRowImage_eq_linearPoint,map_inv,hg,inv_inv]
    let a : hammingSignCode := ⟨affineRowSign 0 v,affineRowSign_mem 0 v⟩
    have hm : ⁅g,rowSignCode a⁆∈S :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    change rowSignHom (Multiplicative.ofAdd ((affineRowSign 0 v∘linearPointEquiv A)-affineRowSign 0 v))∈S.map codeGroup.subtype
    rw [←hr,←rowSignHom_commutator]
    exact ⟨⁅g,rowSignCode a⁆,hm,map_commutatorElement codeGroup.subtype _ _⟩

theorem rowSignCode_mem_of_hammingSigns (S : Subgroup codeGroup)
    (hS : hammingSignCode≤rowSignPreimage S) (a : hammingSignCode) : rowSignCode a∈S := by
  obtain ⟨g,hg,he⟩ := hS a.prop
  have hh : g=rowSignCode a := Subtype.ext he
  exact hh ▸ hg

theorem signKernel_le_commutator_scalars (S : Subgroup codeGroup)
    (hc : commutator codeGroup≤S) (hI : codeI∈S) : codePermutationHom.ker≤S := by
  intro g hg
  let s : signPatterns := (codeSignKernelEquiv ⟨g,hg⟩).toAdd
  let a := hammingSignEquiv.symm s
  have ha := rowSignCode_mem_of_hammingSigns S (hammingSigns_mem_commutator_scalars S hc hI) a
  have he : rowSignCode a=g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · have hh := congrArg Subtype.val (hammingSignEquiv.apply_symm_apply s)
      exact hh
    · exact ((codePermutationHom_kernel g).mp hg).symm
  exact he ▸ ha

end Atlas.Rudvalis

import Atlas.Rudvalis.CodeGaussian

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def codeRowTranslationHom : codeRowKernel →* binaryTranslationSubgroup where
  toFun g := ⟨codePermutationHom g.val,by
    rw [← binaryBlockLinearHom_kernel_translations]
    exact g.prop⟩
  map_one' := Subtype.ext (map_one codePermutationHom)
  map_mul' g h := Subtype.ext (map_mul codePermutationHom g.val h.val)

theorem codeRowTranslationHom_surjective : Function.Surjective codeRowTranslationHom := by
  intro t
  obtain ⟨g,hg⟩ := codePermutationHom_surjective t.val
  have hmem : g∈codeBlockLinearHom.ker := by
    change binaryBlockLinearHom (codePermutationHom g)=1
    rw [hg]
    exact show t.val∈binaryBlockLinearHom.ker from
      (binaryBlockLinearHom_kernel_translations.symm ▸ t.prop)
  exact ⟨⟨g,hmem⟩,Subtype.ext hg⟩

theorem codeRowTranslationHom_kernel (g : codeRowKernel) :
    g∈codeRowTranslationHom.ker ↔ g.val∈codePermutationHom.ker := by
  change codeRowTranslationHom g=1 ↔ codePermutationHom g.val=1
  exact Subtype.ext_iff

noncomputable def codeRowSignKernelEquiv :
    codeRowTranslationHom.ker ≃* codePermutationHom.ker where
  toFun g := ⟨g.val.val,(codeRowTranslationHom_kernel _).mp g.prop⟩
  invFun g := ⟨⟨g.val,by
    change binaryBlockLinearHom (codePermutationHom g.val)=1
    rw [show codePermutationHom g.val=1 from g.prop,map_one]⟩,
    (codeRowTranslationHom_kernel _).mpr g.prop⟩
  left_inv g := rfl
  right_inv g := rfl
  map_mul' g h := rfl

theorem codeRowTranslationHom_kernel_order : Nat.card codeRowTranslationHom.ker=16 := by
  rw [Nat.card_congr codeRowSignKernelEquiv.toEquiv,codePermutationHom_kernel_order]

noncomputable def codeRowMatrixHom : codeRowKernel →* Multiplicative BinaryMatrix :=
  binaryTranslationEquiv.symm.toMonoidHom.comp codeRowTranslationHom

theorem codeRowMatrixHom_surjective : Function.Surjective codeRowMatrixHom :=
  binaryTranslationEquiv.symm.surjective.comp codeRowTranslationHom_surjective


theorem codeI_pow_four : codeI^4=1 := by
  apply Subtype.ext
  apply monomialHom_injective
  change monomialHom (codeI.val^4)=monomialHom 1
  rw [map_pow,map_one,pow_mul _ 2 2]
  simp only [pow_two]
  apply LinearEquiv.ext
  intro w
  simp only [LinearEquiv.mul_apply]
  change monomialHom codeI.val (monomialHom codeI.val
    (monomialHom codeI.val (monomialHom codeI.val w)))=w
  rw [codeI_square_action,codeI_square_action,neg_neg]

theorem codeI_pow_two_ne_one : codeI^2≠1 := by
  intro h
  have hh := congrArg (fun g : codeGroup => monomialHom g.val (fun _ => 1)) h
  change monomialHom (codeI.val^2) (fun _ => 1)=monomialHom 1 (fun _ => 1) at hh
  rw [map_pow,map_one] at hh
  change monomialHom codeI.val (monomialHom codeI.val (fun _ => 1))=(fun _ => 1) at hh
  rw [codeI_square_action] at hh
  have he := congrFun hh (seedCoordinateEquiv (0,0))
  exact (by decide : (-1 : ZMod 4) ≠ 1) he

theorem codeI_order : orderOf codeI=4 := by
  exact orderOf_eq_prime_pow (p:=2) (n:=1) codeI_pow_two_ne_one codeI_pow_four

end Atlas.Rudvalis


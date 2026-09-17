import Atlas.Fischer.CountingPairChoices

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev CountingSourceTypeA := {S : Finset (Fin 6) // S.card=2}
abbrev CountingSourceTypeC := countingHexacode × Fin 6

def countingTypeA_source (t : CountingTypeA) : CountingSourceTypeA :=
  ⟨support t.val.val,countingTypeA_mask_weight t⟩

def countingTypeA_sourceEquiv : CountingTypeA ≃ CountingSourceTypeA :=
  Equiv.ofBijective countingTypeA_source (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_,?_⟩
    · intro t s h
      apply Subtype.ext
      apply Subtype.ext
      exact binarySupportEquiv.injective (congrArg Subtype.val h)
    · rw [← Nat.card_eq_fintype_card,countingTypeA_card,Fintype.card_finset_len,Fintype.card_fin]
      decide)

def countingTypeC_source (t : CountingTypeC) : CountingSourceTypeC :=
  (countingHexEquiv t.1,countingDistinguishedColumn t)

theorem countingTypeC_source_injective : Function.Injective countingTypeC_source := by
  rintro ⟨h,r⟩ ⟨h',r'⟩ he
  have hh : h=h' := countingHexEquiv.injective (congrArg Prod.fst he)
  subst h'
  have hj : countingDistinguishedColumn ⟨h,r⟩=countingDistinguishedColumn ⟨h,r'⟩ := congrArg Prod.snd he
  apply congrArg (fun s : {r : P6 // hammingNorm (c0Encoder (h,r)+eta)=8} => (⟨h,s⟩ : CountingTypeC))
  apply Subtype.ext
  apply Subtype.ext
  have hm : r.val.val+oddMask h.val=r'.val.val+oddMask h.val := by
    change countingOddMask ⟨h,r⟩=countingOddMask ⟨h,r'⟩
    rw [countingDistinguishedColumn_mask,countingDistinguishedColumn_mask,hj]
  exact add_right_cancel hm

/-- Every source pair (hexaword, distinguished column) occurs exactly once. -/
def countingTypeC_sourceEquiv : CountingTypeC ≃ CountingSourceTypeC :=
  Equiv.ofBijective countingTypeC_source (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨countingTypeC_source_injective,?_⟩
    rw [← Nat.card_eq_fintype_card,countingTypeC_card,Fintype.card_prod,Fintype.card_fin,
      ← Nat.card_eq_fintype_card,countingHexacode_card])

def countingSourceOctadEquiv : CountingSourceTypeA ⊕ (CountingSourceTypeB ⊕ CountingSourceTypeC) ≃ Octad :=
  ((Equiv.sumCongr countingTypeA_sourceEquiv
    (Equiv.sumCongr countingTypeB_sourceEquiv countingTypeC_sourceEquiv)).symm).trans countingOctadEquiv

end Atlas.Fischer

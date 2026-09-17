import Atlas.Fischer.CountingOctadDescriptions

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def countingPairTranslation (h : hexacode) : P6 ≃ P6 where
  toFun r := ⟨countingPairMask h r,(parityCode_mem 5 _).mpr (countingPairMask_even h r)⟩
  invFun r := ⟨countingPairMask h r,(parityCode_mem 5 _).mpr (countingPairMask_even h r)⟩
  left_inv r := by apply Subtype.ext; funext i; simp [countingPairMask,add_assoc]
  right_inv r := by apply Subtype.ext; funext i; simp [countingPairMask,add_assoc]

theorem countingPairChoices_iff (h : hexacode) (hh : hammingNorm h.val=4) (r : P6) :
    hammingNorm (c0Encoder (h,r))=8 ↔
      ∀ i : Fin 6, h.val (hexPos i)=0 → countingPairMask h r i=0 := by
  constructor
  · intro hw
    exact countingTypeB_pairMask_zero_off_support ⟨⟨h,hh⟩,⟨r,hw⟩⟩
  · intro hm
    have hz (i : Fin 6) (hi : h.val (hexPos i)=0) : r.val i=0 := by
      have he := hm i hi
      simpa [countingPairMask,hi,qK] using he
    have he : Finset.univ.filter (fun i : Fin 6 => h.val (hexIndexEquiv.symm i)=0 ∧ r.val i ≠ 0)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hc
      exact hc.2 (hz i hc.1)
    rw [c0Encoder_weight_formula,hh,he,Finset.card_empty]

def countingWeightFourHexEquiv : {h : hexacode // hammingNorm h.val=4} ≃
    {h : countingHexacode // hammingNorm h.val=4} :=
  Equiv.subtypeEquiv countingHexEquiv (by
    intro h
    change hammingNorm h.val=4 ↔ hammingNorm (countingHexCoordinates h.val)=4
    rw [countingHexCoordinates_weight])

/-- Every even source mask supported on the four nonzero positions is admitted. -/
abbrev CountingSourceTypeB := Σ h : {h : countingHexacode // hammingNorm h.val=4},
  {e : P6 // ∀ i : Fin 6, h.val.val i=0 → e.val i=0}

def countingTypeB_sourceEquiv : CountingTypeB ≃ CountingSourceTypeB :=
  Equiv.sigmaCongr countingWeightFourHexEquiv (fun h =>
    Equiv.subtypeEquiv (countingPairTranslation h.val) (by
      intro r
      change hammingNorm (c0Encoder (h.val,r))=8 ↔
        ∀ i : Fin 6, countingHexCoordinates h.val.val i=0 → countingPairMask h.val r i=0
      have hz (i : Fin 6) : countingHexCoordinates h.val.val i=0 ↔ h.val.val (hexPos i)=0 := by
        change countingLetterEquiv (countingHexLocal i (h.val.val (hexPos i)))=0 ↔ _
        rw [LinearEquiv.map_eq_zero_iff,LinearEquiv.map_eq_zero_iff]
      simp only [hz]
      exact countingPairChoices_iff h.val h.property r))

theorem countingSourceTypeB_card : Nat.card CountingSourceTypeB=360 := by
  rw [← Nat.card_congr countingTypeB_sourceEquiv,countingTypeB_card]

end Atlas.Fischer

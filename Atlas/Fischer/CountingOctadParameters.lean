import Atlas.Fischer.CountingHexacodeComparison
import Atlas.Codes.GolayCounts
import Atlas.Fischer.CoordinateEvaluation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Original parity masks for two complete tetrads. -/
abbrev CountingTypeA := {r : P6 // hammingNorm (c0Encoder (0,r))=8}
/-- Original weight-four hexawords and their eight valid even pair choices. -/
abbrev CountingTypeB := Σ h : {h : hexacode // hammingNorm h.val=4},
  {r : P6 // hammingNorm (c0Encoder (h.val,r))=8}
/-- Original odd-coset parameters; each hexaword has six distinguished columns. -/
abbrev CountingTypeC := Σ h : hexacode, {r : P6 // hammingNorm (c0Encoder (h,r)+eta)=8}

abbrev CountingOctadParameters := CountingTypeA ⊕ (CountingTypeB ⊕ CountingTypeC)

theorem countingTypeA_card : Nat.card CountingTypeA=15 := by
  have h := c0_weight_zero_count 2
  norm_num [Nat.choose] at h
  simpa only [Nat.card_eq_fintype_card] using h

theorem countingWeightFourHex_card : Nat.card {h : hexacode // hammingNorm h.val=4}=45 := by
  have h := hexacode_weight_distribution 4
  simpa [hexWeightCount,Nat.card_eq_fintype_card,Fintype.card_subtype] using h

theorem countingTypeB_card : Nat.card CountingTypeB=360 := by
  rw [Nat.card_sigma]
  have hf (h : {h : hexacode // hammingNorm h.val=4}) :
      Nat.card {r : P6 // hammingNorm (c0Encoder (h.val,r))=8}=8 := by
    simpa using c0_weight_four_count h.val h.property 0
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card,countingWeightFourHex_card]

theorem countingTypeC_card : Nat.card CountingTypeC=384 := by
  rw [Nat.card_sigma]
  have hf (h : hexacode) : Nat.card {r : P6 // hammingNorm (c0Encoder (h,r)+eta)=8}=6 :=
    (odd_word_counts h).1
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card,hexacode_card]

theorem countingOctadParameters_card : Nat.card CountingOctadParameters=759 := by
  rw [Nat.card_sum,Nat.card_sum,countingTypeA_card,countingTypeB_card,countingTypeC_card]

def countingOctadRaw : CountingOctadParameters → hexacode × P6 × Bit
  | Sum.inl r => (0,r.val,0)
  | Sum.inr (Sum.inl p) => (p.1.val,p.2.val,0)
  | Sum.inr (Sum.inr p) => (p.1,p.2.val,1)

def countingOctadCode (p : CountingOctadParameters) : golay := golayEquiv (countingOctadRaw p)

theorem countingOctadCode_weight (p : CountingOctadParameters) :
    hammingNorm (countingOctadCode p).val=8 := by
  rcases p with r | (⟨h,r⟩ | ⟨h,r⟩)
  · simpa [countingOctadCode,countingOctadRaw,golayEquiv_apply,c0Encoder] using r.property
  · simpa [countingOctadCode,countingOctadRaw,golayEquiv_apply,c0Encoder] using r.property
  · simpa [countingOctadCode,countingOctadRaw,golayEquiv_apply,c0Encoder] using r.property

end Atlas.Fischer

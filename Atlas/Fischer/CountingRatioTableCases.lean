import Atlas.Fischer.CountingRatioTable

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def CountingRatioConstantMultiplicity (g h : countingHexacode) : Prop :=
  Nat.card {w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} //
    countingRatioOnes g w.val=countingHexSupport g ∩ countingHexSupport h}=1 ∧
  Nat.card {w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} //
    countingRatioOnes g w.val=∅}=2

/-- Both overlap-two rows of the source ratio table, with all hypotheses derived. -/
theorem countingRatioTable_overlap_two (g h : countingHexacode)
    (hh : hammingNorm h.val=4) (hi : (countingHexSupport g ∩ countingHexSupport h).card=2) :
    CountingRatioConstantMultiplicity g h := by
  obtain ⟨r,hr0,hr⟩ := countingHex_ratios_two_constant g h hi
  have hn : (countingHexSupport g ∩ countingHexSupport h).Nonempty :=
    Finset.card_pos.mp (by omega)
  exact countingRatioOnes_constant_card g h hh hn r hr0 hr

/-- Both overlap-four rows of the source ratio table, with no proportionality premise. -/
theorem countingRatioTable_overlap_four (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hh : hammingNorm h.val=4)
    (hi : (countingHexSupport g ∩ countingHexSupport h).card=4) :
    CountingRatioConstantMultiplicity g h := by
  have hsG : countingHexSupport g ∩ countingHexSupport h=countingHexSupport g :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [countingHexSupport_card,hg,hi])
  have hsH : countingHexSupport g ∩ countingHexSupport h=countingHexSupport h :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [countingHexSupport_card,hh,hi])
  obtain ⟨r,hr0,hr⟩ := countingHex_ratios_same_support g h hg (hsG.symm.trans hsH)
  have hn : (countingHexSupport g ∩ countingHexSupport h).Nonempty :=
    Finset.card_pos.mp (by omega)
  exact countingRatioOnes_constant_card g h hh hn r hr0 hr

end Atlas.Fischer

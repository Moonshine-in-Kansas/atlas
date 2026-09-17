import Atlas.Fischer.CountingBPairColumns
import Atlas.Fischer.CountingRatioWeightedSums

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The three-word ratio subtotal, with an actual even mask. -/
def countingBMaskHistogram (p : CountingProfileData) (T : Finset (Fin 6))
    (e : P6) (j : Fin 6) : ℕ :=
  let I := p.support ∩ T
  if I.card=3 then
    ∑ i ∈ I, countingWeightHistogram
      (p.weight (countingTypeBColumnProfile T) (countingBPairColumns I {i} e)) j
  else countingWeightHistogram
    (p.weight (countingTypeBColumnProfile T) (countingBPairColumns I I e)) j+
    2*countingWeightHistogram
      (p.weight (countingTypeBColumnProfile T) (countingBPairColumns I ∅ e)) j

theorem countingBMaskHistogram_parity (p : CountingProfileData) (ht : p.sourceType=1)
    (T : Finset (Fin 6)) (m : Fin 5 → Bit) (j : Fin 6) :
    countingBMaskHistogram p T (parityEquiv 5 m) j=p.wordHistogramB T m j := by
  simp only [countingBMaskHistogram,CountingProfileData.wordHistogramB,ht,
    show (1 : Fin 3)≠0 by decide,show (1 : Fin 3)≠2 by decide,if_false,
    countingBPairColumns_parity]

theorem countingSourceBB_word_sum (p : CountingProfileData)
    (g : {g : countingHexacode // hammingNorm g.val=4})
    (hg : ∀ i, p.g i=if g.val.val i=0 then 0 else 2)
    (T : CountingFourSupport) (e : CountingMaskOn T.val) (j : Fin 6) :
    (∑ h : CountingWordOn T.val, countingWeightHistogram
      (countingSourceWeight p.epsilon p.D p.E p.F
        (.inr (.inl ⟨g,⟨0,by intros; rfl⟩⟩)) (.inr (.inl (countingSourceBGrouped T e h)))) j)=
      countingBMaskHistogram p T.val e.val j := by
  have hs : p.support=countingHexSupport g.val := by
    ext i
    simp only [CountingProfileData.support,countingHexSupport,Finset.mem_filter,
      Finset.mem_univ,true_and]
    by_cases hi : g.val.val i=0 <;> simp [hg,hi]
  obtain ⟨h⟩ : Nonempty (CountingWordOn T.val) :=
    (Nat.card_pos_iff.mp (by rw [countingHexSupport_fiber_card T.val T.property]; omega)).1
  have hh : hammingNorm h.val.val=4 := by rw [← countingHexSupport_card,h.property]; exact T.property
  have hw := countingRatioOnes_sum g.val h.val g.property hh
    (fun Z => countingWeightHistogram (p.weight (countingTypeBColumnProfile T.val)
      (countingBPairColumns (countingHexSupport g.val ∩ T.val) Z e.val)) j)
  rw [h.property] at hw
  simp only [countingSourceBB_weight p g hg,countingBMaskHistogram,hs]
  exact hw

/-- The entire Type B target subtotal for every normalized actual Type B source.
The support, mask and three-word fibers are all the actual source-code fibers. -/
theorem countingProfile_actual_BB (p : CountingProfileData)
    (g : {g : countingHexacode // hammingNorm g.val=4})
    (ht : p.sourceType=1) (hg : ∀ i, p.g i=if g.val.val i=0 then 0 else 2) :
    countingSourceBTargetHistogram p.epsilon p.D p.E p.F
      (.inr (.inl ⟨g,⟨0,by intros; rfl⟩⟩))=p.histogramB := by
  funext j
  simp only [countingSourceBTargetHistogram]
  rw [countingSourceBGrouped_sum]
  simp_rw [countingSourceBB_word_sum p g hg]
  have hT (T : CountingFourSupport) :
      (∑ e : CountingMaskOn T.val, countingBMaskHistogram p T.val e.val j)=
        ∑ m : Fin 5 → Bit, if countingTableMaskSupported T.val m then p.wordHistogramB T.val m j else 0 := by
    rw [countingMaskOn_sum T.val (fun e => countingBMaskHistogram p T.val e j)]
    simp_rw [countingBMaskHistogram_parity p ht]
  simp_rw [hT]

  change (∑ T : CountingFourSupport, ∑ m : Fin 5 → Bit,
    if countingTableMaskSupported T.val m then p.wordHistogramB T.val m j else 0)=_
  let e : CountingFourSupport ≃ ↥((Finset.univ : Finset (Fin 6)).powersetCard 4) :=
    Equiv.subtypeEquivRight (by intro T; simp)
  let f (T : Finset (Fin 6)) := ∑ m : Fin 5 → Bit,
    if countingTableMaskSupported T m then p.wordHistogramB T m j else 0
  change (∑ T : CountingFourSupport, f T.val)=∑ T ∈ Finset.univ.powersetCard 4, f T
  calc
    _ = ∑ T : ↥((Finset.univ : Finset (Fin 6)).powersetCard 4), f T.val :=
      Equiv.sum_comp e (fun T => f T.val)
    _ = _ := by
      rw [Finset.sum_coe_sort_eq_attach]
      exact Finset.sum_attach _ f

end Atlas.Fischer

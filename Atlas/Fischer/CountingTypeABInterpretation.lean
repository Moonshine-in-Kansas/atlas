import Atlas.Fischer.CountingGroupedBParameters
import Atlas.Fischer.CountingTypeACrossInterpretation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem countingGroupedB_column_card (T : CountingFourSupport)
    (e : CountingMaskOn T.val) (h : CountingWordOn T.val) (i : Fin 6) :
    (countingSourceColumn (.inr (.inl (countingSourceBGrouped T e h))) i).card=
      countingTypeBColumnProfile T.val i := by
  rw [countingSourceColumn_card_B]
  have hs : i ∈ T.val ↔ h.val.val i ≠ 0 := by
    simpa only [h.property] using (show i ∈ countingHexSupport h.val ↔ h.val.val i ≠ 0 by simp [countingHexSupport])
  change (if h.val.val i=0 then 0 else 2)=_
  by_cases hi : h.val.val i=0 <;> simp [countingTypeBColumnProfile,hs,hi]

/-- Regroup the actual Type B target parameters and count their three words on
 each support, retaining the entire supported parity-mask sum. -/
theorem countingGroupedB_histogram_sum (f : CountingSourceTypeB → ℕ)
    (g : Finset (Fin 6) → P6 → ℕ)
    (hf : ∀ T e h, f (countingSourceBGrouped T e h)=g T.val e.val) :
    (∑ b, f b)=∑ T ∈ Finset.univ.powersetCard 4, ∑ m : Fin 5 → Bit,
      if countingTableMaskSupported T m then 3*g T (parityEquiv 5 m) else 0 := by
  rw [countingSourceBGrouped_sum]
  have hw (T : CountingFourSupport) : Fintype.card (CountingWordOn T.val)=3 := by
    simpa only [Nat.card_eq_fintype_card] using countingHexSupport_fiber_card T.val T.property
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,hw]
  conv_lhs => arg 2; ext T; rw [countingMaskOn_sum T.val (fun e => 3*g T.val e)]
  let e : CountingFourSupport ≃ ↥((Finset.univ : Finset (Fin 6)).powersetCard 4) :=
    Equiv.subtypeEquivRight (by intro T; simp)
  let k (T : Finset (Fin 6)) := ∑ m : Fin 5 → Bit,
      if countingTableMaskSupported T m then 3*g T (parityEquiv 5 m) else 0
  change (∑ T : CountingFourSupport, k T.val)=∑ T ∈ Finset.univ.powersetCard 4,k T
  calc
    _ = ∑ T : ↥((Finset.univ : Finset (Fin 6)).powersetCard 4), k T.val :=
      Equiv.sum_comp e (fun T => k T.val)
    _ = _ := by
      rw [Finset.sum_coe_sort_eq_attach]
      exact Finset.sum_attach _ k

/-- Exact Type B target subtotal for an actual Type A source. -/
theorem countingProfile_actual_AB (p : CountingProfileData) (a : CountingSourceTypeA)
    (ht : p.sourceType=0) (hg : ∀ i, p.g i=if i ∈ a.val then 4 else 0) :
    countingSourceBTargetHistogram p.epsilon p.D p.E p.F (.inl a)=p.histogramB := by
  have hw (T : CountingFourSupport) (e : CountingMaskOn T.val) (h : CountingWordOn T.val) :
      countingSourceWeight p.epsilon p.D p.E p.F (.inl a)
        (.inr (.inl (countingSourceBGrouped T e h)))=
      p.weight (countingTypeBColumnProfile T.val)
        (fun i => if p.g i=4 then countingTypeBColumnProfile T.val i else 0) := by
    simp only [countingSourceWeight,CountingProfileData.weight,countingSourceColumn_card_A,
      countingSourceA_joint_card,countingGroupedB_column_card]
    congr 1
    · funext i; exact (hg i).symm
    · funext i; by_cases hi : i ∈ a.val <;> simp [hg,hi]
  funext j
  unfold countingSourceBTargetHistogram
  rw [countingGroupedB_histogram_sum _
    (fun T _ => countingWeightHistogram (p.weight (countingTypeBColumnProfile T)
      (fun i => if p.g i=4 then countingTypeBColumnProfile T i else 0)) j)
    (by intro T e h; rw [hw])]
  simp only [CountingProfileData.histogramB,CountingProfileData.wordHistogramB,ht,ite_true]

end Atlas.Fischer

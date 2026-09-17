import Atlas.Fischer.CountingSourceParameters

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The eight pair choices over each particular weight-four source word. -/
theorem countingSourceMask_card (h : countingHexacode) (hh : hammingNorm h.val=4) :
    Nat.card {e : P6 // ∀ i : Fin 6, h.val i=0 → e.val i=0}=8 := by
  obtain ⟨w,rfl⟩ := countingHexEquiv.surjective h
  have hw : hammingNorm w.val=4 := by
    change hammingNorm (countingHexCoordinates w.val)=4 at hh
    rwa [countingHexCoordinates_weight] at hh
  let f : {r : P6 // hammingNorm (c0Encoder (w,r))=8} ≃
      {e : P6 // ∀ i : Fin 6, (countingHexEquiv w).val i=0 → e.val i=0} :=
    Equiv.subtypeEquiv (countingPairTranslation w) (by
      intro r
      change hammingNorm (c0Encoder (w,r))=8 ↔
        ∀ i : Fin 6, countingHexCoordinates w.val i=0 → countingPairMask w r i=0
      have hz (i : Fin 6) : countingHexCoordinates w.val i=0 ↔ w.val (hexPos i)=0 := by
        change countingLetterEquiv (countingHexLocal i (w.val (hexPos i)))=0 ↔ _
        rw [LinearEquiv.map_eq_zero_iff,LinearEquiv.map_eq_zero_iff]
      simp only [hz]
      exact countingPairChoices_iff w hw r)
  rw [← Nat.card_congr f]
  simpa using c0_weight_four_count w hw 0

end Atlas.Fischer

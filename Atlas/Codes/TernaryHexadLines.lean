import Atlas.Codes.TernaryHexadProjection

namespace Atlas.Codes

/-- The actual codewords supported on a hexad form exactly its one-dimensional line. -/
theorem ternaryGolay_supported_hexad (c : TernarySixWords) (w : ternaryGolay)
    (hw : ternarySupport w.val ⊆ ternarySupport c.val.val) :
    ∃ a : ZMod 3,w.val=a • c.val.val := by
  by_cases hz : w.val=0
  · exact ⟨0,by simpa using hz⟩
  have hm := ternaryGolay_minimum _ w.prop hz
  have hc : (ternarySupport c.val.val).card=6 := c.prop
  have hs : ternarySupport w.val=ternarySupport c.val.val :=
    Finset.eq_of_subset_of_card_le hw (by simpa only [hc,ternarySupport_card] using hm)
  have hweight : ternaryWeight w.val=6 := by rw [← ternarySupport_card,hs,hc]
  have hi : 5 ≤ (ternarySupport c.val.val ∩ ternarySupport w.val).card := by
    rw [hs,Finset.inter_self,hc]; decide
  rcases ternaryGolay_hexad_intersection _ _ c.val.prop w.prop c.prop hweight hi with he | he
  · exact ⟨1,by simpa using he⟩
  · exact ⟨-1,by simpa using he⟩

end Atlas.Codes

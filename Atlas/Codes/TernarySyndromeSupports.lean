import Atlas.Codes.TernaryAffineSyndromes
import Atlas.Codes.TernaryGolaySupports

noncomputable section
namespace Atlas.Codes

theorem ternarySupport_sub_subset (u v : TernaryWord) :
    ternarySupport (u-v) ⊆ ternarySupport u ∪ ternarySupport v := by
  intro i hi
  simp only [ternarySupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Pi.sub_apply, Finset.mem_union] at hi ⊢
  by_contra h
  push_neg at h
  exact hi (by rw [h.1, h.2, sub_self])

theorem ternarySyndromeClass_eq_iff (u v : TernaryWord) :
    ternarySyndromeClass u = ternarySyndromeClass v ↔ u-v ∈ ternaryGolay :=
  Submodule.Quotient.eq _

theorem ternarySyndrome_union_support (u v : TernaryWord)
    (hsize : (ternarySupport u ∪ ternarySupport v).card < 6)
    (he : ternarySyndromeClass u = ternarySyndromeClass v) : u = v := by
  have hc := ternarySyndromeClass_eq_iff u v |>.mp he
  by_contra hne
  have hm := ternaryGolay_minimum (u-v) hc (sub_ne_zero.mpr hne)
  have hb := Finset.card_le_card (ternarySupport_sub_subset u v)
  change ternaryWeight (u-v) ≤ _ at hb
  omega

/-- The minimum six makes distinct words of combined support at most five
have distinct actual code syndromes. -/
theorem ternarySyndrome_small_support (u v : TernaryWord)
    (hsize : (ternarySupport u).card + (ternarySupport v).card < 6)
    (he : ternarySyndromeClass u = ternarySyndromeClass v) : u = v := by
  have hc := ternarySyndromeClass_eq_iff u v |>.mp he
  by_contra hne
  have hm := ternaryGolay_minimum (u-v) hc (sub_ne_zero.mpr hne)
  have hb := (Finset.card_le_card (ternarySupport_sub_subset u v)).trans
    (Finset.card_union_le _ _)
  change ternaryWeight (u-v) ≤ _ at hb
  omega

end Atlas.Codes

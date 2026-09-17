import Atlas.Fischer.CubicTriangleCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Precisely the two intersection types used by the signed contraction. -/
def OctadPairAdmissible (D E : Octad) : Prop :=
  (D.val ∩ E.val).card = 4 ∨ (D.val ∩ E.val).card = 0

def octadDiamond (D E : Octad) (h : OctadPairAdmissible D E) : Octad :=
  if h4 : (D.val ∩ E.val).card = 4 then cubicSextetCompletion D E h4
  else cubicTrioCompletion D E (h.resolve_left h4)

def octadDelta (D E : Octad) : ℕ :=
  if (D.val ∩ E.val).card = 0 then 1 else 0

theorem octadDelta_le_one (D E : Octad) : octadDelta D E ≤ 1 := by
  classical
  unfold octadDelta
  split_ifs <;> omega

theorem octadDiamond_word (D E : Octad) (h : OctadPairAdmissible D E) :
    octadWord (octadDiamond D E h) = octadWord D + octadWord E +
      if (D.val ∩ E.val).card = 0 then golayOne else 0 := by
  classical
  by_cases h4 : (D.val ∩ E.val).card = 4
  · rw [octadDiamond, dif_pos h4, cubicSextetCompletion_word]
    have h0 : (D.val ∩ E.val).card ≠ 0 := by omega
    simp [h0]
  · rw [octadDiamond, dif_neg h4, cubicTrioCompletion_word]
    simp [h.resolve_left h4]

theorem octadPairAdmissible_of_triangle (D E F : Octad)
    (h : octadWord F = octadWord D + octadWord E ∨
      octadWord F = octadWord D + octadWord E + golayOne) : OctadPairAdmissible D E := by
  rcases h with h | h
  · left
    simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
      octadWord_sum_weight F D E h
  · right
    simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
      octadWord_complementary_sum_weight F D E h

end Atlas.Fischer

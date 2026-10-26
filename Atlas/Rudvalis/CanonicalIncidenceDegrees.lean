import Atlas.Rudvalis.CanonicalIncidenceTransport
import Atlas.Rudvalis.CanonicalFrameCount

namespace Atlas.Rudvalis

/-- Every actual minimal cross lies in exactly 2925 intrinsic canonical frames. -/
theorem canonicalFramesThroughCross_card (x : MinimalCross) :
    Nat.card (CanonicalFramesThroughCross x)=2925 := by
  have h := canonicalFramesThroughCross_incidence x
  rw [rudvalisLattice_minimal_cross_card,canonicalBases_card] at h
  omega

theorem canonicalFrame_couples_card (F : canonicalBases) :
    Nat.card {c : IntrinsicCouples // c.val⊆F.val}=378 := by
  have hF := canonicalFrame_isFrame F.val F.prop
  rw [couplesWithin_card F.val (isFrame_finite hF) hF.2,hF.1]
  rfl

theorem canonicalFramesThroughCouple_incidence (c : Set MinimalCross) (hc : IsCouple c) :
    Nat.card IntrinsicCouples*Nat.card (CanonicalFramesThroughCouple c)=Nat.card canonicalBases*378 := by
  apply Atlas.Combinatorics.uniform_incidence_card
    (fun d : IntrinsicCouples=>fun F : canonicalBases=>d.val⊆F.val)
  · intro d
    rw [canonicalFramesThroughCouple_card_reference d.val d.prop,
      canonicalFramesThroughCouple_card_reference c hc]
  · exact canonicalFrame_couples_card

/-- Every actual orthogonal couple lies in exactly 45 intrinsic canonical frames. -/
theorem canonicalFramesThroughCouple_card (c : Set MinimalCross) (hc : IsCouple c) :
    Nat.card (CanonicalFramesThroughCouple c)=45 := by
  have h := canonicalFramesThroughCouple_incidence c hc
  rw [intrinsicCouples_card,canonicalBases_card] at h
  omega

end Atlas.Rudvalis

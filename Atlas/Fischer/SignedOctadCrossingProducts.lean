import Atlas.Fischer.SignedOctadProductFormulas
import Atlas.Mathieu.HeptadIntersections

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem product_signedOctads_two (d f : SignedOctad)
    (h : signedOctadIntersection d f = 2) :
    product (signedOctadVector d) (signedOctadVector f) = 0 := by
  have hn := signedOctadSupport_ne_of_intersection d f (by omega)
  have hc : signedOctadIntersection (canonicalOctadLift (signedOctadSupport d))
      (canonicalOctadLift (signedOctadSupport f)) = 2 := by
    have hh := h
    rw [signedOctad_sign_section d,signedOctad_sign_section f,signedOctadIntersection_sign] at hh
    exact hh
  simpa only [← signedOctad_sign_section d,← signedOctad_sign_section f] using
    product_signed_sections_two d.val.2 f.val.2 (signedOctadSupport d) (signedOctadSupport f) hn hc

theorem signedOctadIntersection_eq_eight_iff (d f : SignedOctad) :
    signedOctadIntersection d f = 8 ↔ signedOctadSupport d = signedOctadSupport f := by
  constructor
  · intro h
    apply Subtype.ext
    have hd : (signedOctadSupport d).val ∩ (signedOctadSupport f).val =
        (signedOctadSupport d).val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        change _ ≤ signedOctadIntersection d f
        rw [h,octad_size _ (signedOctadSupport d).property])
    have hf : (signedOctadSupport d).val ∩ (signedOctadSupport f).val =
        (signedOctadSupport f).val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        change _ ≤ signedOctadIntersection d f
        rw [h,octad_size _ (signedOctadSupport f).property])
    exact hd.symm.trans hf
  · intro h
    unfold signedOctadIntersection
    rw [h,Finset.inter_self]
    exact octad_size _ (signedOctadSupport f).property

/-- The literal signed product table, with actual Parker product labels. -/
theorem product_signedOctads_distinct (d f : SignedOctad)
    (hne : signedOctadSupport d ≠ signedOctadSupport f) :
    (2 : Scalar) • product (signedOctadVector d) (signedOctadVector f) =
      (if h : signedOctadIntersection d f = 4 then
        signedOctadVector (octadProductFour d f h) else 0) +
      (if h : signedOctadIntersection d f = 0 then
        theta • signedOctadVector (octadProductDisjoint d f h) else 0) := by
  have h := octad_intersection_sizes _ _ (signedOctadSupport d).property
    (signedOctadSupport f).property
  change signedOctadIntersection d f = 0 ∨ signedOctadIntersection d f = 2 ∨
    signedOctadIntersection d f = 4 ∨ signedOctadIntersection d f = 8 at h
  rcases h with h | h | h | h
  · simpa [h] using product_signedOctads_disjoint d f h
  · simp [h,product_signedOctads_two d f h]
  · simpa [h] using product_signedOctads_four d f h
  · exact (hne ((signedOctadIntersection_eq_eight_iff d f).mp h)).elim

end Atlas.Fischer

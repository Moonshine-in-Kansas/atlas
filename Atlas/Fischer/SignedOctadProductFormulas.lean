import Atlas.Fischer.ParkerSignedProductTable

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

theorem signedOctadSupport_ne_of_intersection (d f : SignedOctad)
    (h : signedOctadIntersection d f ≠ 8) : signedOctadSupport d ≠ signedOctadSupport f := by
  intro he
  apply h
  unfold signedOctadIntersection
  rw [he,Finset.inter_self]
  exact octad_size _ (signedOctadSupport f).property

theorem product_signedOctads_four (d f : SignedOctad)
    (h : signedOctadIntersection d f = 4) :
    (2 : Scalar) • product (signedOctadVector d) (signedOctadVector f) =
      signedOctadVector (octadProductFour d f h) := by
  have hn := signedOctadSupport_ne_of_intersection d f (by omega)
  have hc : signedOctadIntersection (canonicalOctadLift (signedOctadSupport d))
      (canonicalOctadLift (signedOctadSupport f)) = 4 := by
    have hh := h
    rw [signedOctad_sign_section d,signedOctad_sign_section f,signedOctadIntersection_sign] at hh
    exact hh
  simpa only [← signedOctad_sign_section d,← signedOctad_sign_section f] using
    product_signed_sections_four d.val.2 f.val.2 (signedOctadSupport d) (signedOctadSupport f) hn hc

theorem product_signedOctads_disjoint (d f : SignedOctad)
    (h : signedOctadIntersection d f = 0) :
    (2 : Scalar) • product (signedOctadVector d) (signedOctadVector f) =
      theta • signedOctadVector (octadProductDisjoint d f h) := by
  have hn := signedOctadSupport_ne_of_intersection d f (by omega)
  have hc : signedOctadIntersection (canonicalOctadLift (signedOctadSupport d))
      (canonicalOctadLift (signedOctadSupport f)) = 0 := by
    have hh := h
    rw [signedOctad_sign_section d,signedOctad_sign_section f,signedOctadIntersection_sign] at hh
    exact hh
  simpa only [← signedOctad_sign_section d,← signedOctad_sign_section f] using
    product_signed_sections_disjoint d.val.2 f.val.2 (signedOctadSupport d) (signedOctadSupport f) hn hc

end Atlas.Fischer

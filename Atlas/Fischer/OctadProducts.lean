import Atlas.Fischer.SignedOctads
import Atlas.Fischer.Cocode

namespace Atlas.Fischer
open Atlas.Codes

noncomputable def signedOctadIntersection (d f : SignedOctad) : ℕ :=
  ((signedOctadSupport d).val ∩ (signedOctadSupport f).val).card

theorem signedOctadIntersection_overlap (d f : SignedOctad) :
    signedOctadIntersection d f = overlap (d.val.1 : BinaryWord) (f.val.1 : BinaryWord) :=
  (overlap_inter _ _).symm

theorem octad_product_four_weight (d f : SignedOctad)
    (h : signedOctadIntersection d f = 4) :
    hammingNorm ((parkerLoopMultiply d.val f.val).1 : BinaryWord) = 8 := by
  have hw := binary_weight_add (d.val.1 : BinaryWord) (f.val.1 : BinaryWord)
  rw [← signedOctadIntersection_overlap, h, d.prop, f.prop] at hw
  change hammingNorm ((d.val.1 : BinaryWord) + (f.val.1 : BinaryWord)) = 8
  omega

theorem octad_product_disjoint_weight (d f : SignedOctad)
    (h : signedOctadIntersection d f = 0) :
    hammingNorm ((parkerLoopMultiply (parkerLoopMultiply d.val f.val)
      (golayOne, 0)).1 : BinaryWord) = 8 := by
  have hw := binary_weight_add (d.val.1 : BinaryWord) (f.val.1 : BinaryWord)
  rw [← signedOctadIntersection_overlap, h, d.prop, f.prop] at hw
  have hc := complement_weight ((d.val.1 : BinaryWord) + (f.val.1 : BinaryWord))
  change hammingNorm (((d.val.1 : BinaryWord) + (f.val.1 : BinaryWord)) + allOnes) = 8
  omega

/-- The actual loop product label in the intersection-four branch. -/
noncomputable def octadProductFour (d f : SignedOctad)
    (h : signedOctadIntersection d f = 4) : SignedOctad :=
  ⟨parkerLoopMultiply d.val f.val, octad_product_four_weight d f h⟩

/-- The explicitly parenthesized complementary-octad label (df)Ω. -/
noncomputable def octadProductDisjoint (d f : SignedOctad)
    (h : signedOctadIntersection d f = 0) : SignedOctad :=
  ⟨parkerLoopMultiply (parkerLoopMultiply d.val f.val) (golayOne, 0),
    octad_product_disjoint_weight d f h⟩

end Atlas.Fischer

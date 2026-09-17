import Atlas.Fischer.OctadQuadrilateralSigns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The six actual Parker signs in a quintic contraction, including its
external triangle, reduce to the geometric interchange parity. -/
theorem parkerOmegaFactorSet_octad_contraction (i : Omega) (D E G H : Octad)
    (hDE : OctadPairAdmissible D E) (hGH : OctadPairAdmissible G H)
    (hDG : OctadPairAdmissible D G) (hEH : OctadPairAdmissible E H) :
    parkerOmegaFactorSet i (octadWord D) (octadWord E) +
      parkerOmegaFactorSet i (octadWord G) (octadWord H) +
      parkerOmegaFactorSet i (octadWord D) (octadWord G) +
      parkerOmegaFactorSet i (octadWord E) (octadWord H) +
      parkerOmegaFactorSet i (octadWord (octadDiamond D G hDG))
        (octadWord (octadDiamond E H hEH)) +
      parkerOmegaFactorSet i (octadWord (octadDiamond D E hDE))
        (octadWord (octadDiamond G H hGH)) =
      (((E.val ∩ G.val).card / 2 + (D.val ∩ E.val ∩ H.val).card +
        (D.val ∩ G.val ∩ H.val).card : ℕ) : ParkerBit) := by
  rw [parkerOmegaFactorSet_diamond_left, parkerOmegaFactorSet_diamond_right,
    parkerOmegaFactorSet_diamond_left, parkerOmegaFactorSet_diamond_right]
  change parkerChangedFactorSet _ _ _ + parkerChangedFactorSet _ _ _ +
    parkerChangedFactorSet _ _ _ + parkerChangedFactorSet _ _ _ +
    parkerChangedFactorSet _ _ _ + parkerChangedFactorSet _ _ _ = _
  rw [parkerChangedFactorSet_interchange, overlap_inter, octadWord_support,
    octadWord_support, parkerTripleIntersection_octads, parkerTripleIntersection_octads]
  simp only [Nat.cast_add]

end Atlas.Fischer

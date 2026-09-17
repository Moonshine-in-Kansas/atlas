import Atlas.Fischer.ParkerQuadrilateral
import Atlas.Fischer.OctadDiamond
import Atlas.Fischer.OctadShortenedCode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem parkerTripleIntersection_octads (D F G : Octad) :
    parkerTripleIntersection (octadWord D) (octadWord F) (octadWord G) =
      ((D.val ∩ F.val ∩ G.val).card : ParkerBit) := by
  classical
  have he : D.val ∩ F.val ∩ G.val =
      Finset.univ.filter (fun i => i ∈ D.val ∧ i ∈ F.val ∧ i ∈ G.val) := by
    ext i
    simp [and_assoc]
  rw [he, Finset.card_filter, Nat.cast_sum]
  unfold parkerTripleIntersection
  apply Finset.sum_congr rfl
  intro i _
  simp only [octadWord_apply]
  by_cases hd : i ∈ D.val <;> by_cases hf : i ∈ F.val <;>
    by_cases hg : i ∈ G.val <;> simp [hd, hf, hg]

theorem octadPairAdmissible_halfOverlap (D F : Octad) (h : OctadPairAdmissible D F) :
    (overlap (octadWord D : BinaryWord) (octadWord F) / 2 : ℕ) = (0 : ParkerBit) := by
  rw [overlap_inter, octadWord_support, octadWord_support]
  rcases h with h | h <;> rw [h] <;> decide

theorem parkerOmegaFactorSet_diamond_left (i : Omega) (D F : Octad)
    (h : OctadPairAdmissible D F) (w : golay) :
    parkerOmegaFactorSet i (octadWord (octadDiamond D F h)) w =
      parkerOmegaFactorSet i (octadWord D + octadWord F) w := by
  classical
  rw [octadDiamond_word]
  split_ifs <;> simp only [parkerOmegaFactorSet_shift_left, add_zero]

theorem parkerOmegaFactorSet_diamond_right (i : Omega) (D F : Octad)
    (h : OctadPairAdmissible D F) (w : golay) :
    parkerOmegaFactorSet i w (octadWord (octadDiamond D F h)) =
      parkerOmegaFactorSet i w (octadWord D + octadWord F) := by
  classical
  rw [octadDiamond_word]
  split_ifs <;> simp only [parkerOmegaFactorSet_shift_right, add_zero]

/-- The four actual calibrated Parker signs reduce to triple-intersection
parity, uniformly over every admissible retained octad configuration. -/
theorem parkerOmegaFactorSet_octad_quadrilateral (i : Omega) (D F G : Octad)
    (hDF : OctadPairAdmissible D F) (hDG : OctadPairAdmissible D G) :
    parkerOmegaFactorSet i (octadWord F) (octadWord G) +
      parkerOmegaFactorSet i (octadWord (octadDiamond D F hDF))
        (octadWord (octadDiamond D G hDG)) +
      parkerOmegaFactorSet i (octadWord D) (octadWord F) +
      parkerOmegaFactorSet i (octadWord D) (octadWord G) =
        ((D.val ∩ F.val ∩ G.val).card : ParkerBit) := by
  rw [parkerOmegaFactorSet_diamond_left, parkerOmegaFactorSet_diamond_right]
  change parkerChangedFactorSet _ _ _ + parkerChangedFactorSet _ _ _ +
    parkerChangedFactorSet _ _ _ + parkerChangedFactorSet _ _ _ = _
  rw [parkerChangedFactorSet_quadrilateral, octadWord_square_sign,
    octadPairAdmissible_halfOverlap D F hDF, zero_add, zero_add,
    parkerTripleIntersection_octads]

end Atlas.Fischer

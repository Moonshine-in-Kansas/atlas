import Atlas.Fischer.CubicQuadrilateralCounts
import Atlas.Fischer.OctadDiamond

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicOctadTripleCount (D F G : Octad) :
    parkerTripleCount (octadWord F).val (octadWord G).val (octadWord D).val =
      ((D.val ∩ F.val) ∩ G.val).card := by
  unfold parkerTripleCount
  simp only [octadWord_apply]
  have he (i : Omega) :
      (if (if i ∈ F.val then (1 : Bit) else 0) ≠ 0 ∧
        (if i ∈ G.val then (1 : Bit) else 0) ≠ 0 ∧
        (if i ∈ D.val then (1 : Bit) else 0) ≠ 0 then 1 else 0 : ℕ) =
      if i ∈ (D.val ∩ F.val) ∩ G.val then 1 else 0 := by
    by_cases hd : i ∈ D.val <;> by_cases hf : i ∈ F.val <;>
      by_cases hg : i ∈ G.val <;> simp [hd,hf,hg]
  simp_rw [he]
  rw [← Finset.sum_filter,Finset.sum_const]
  have hs : Finset.univ.filter (fun i : Omega => i ∈ (D.val ∩ F.val) ∩ G.val) =
      (D.val ∩ F.val) ∩ G.val := by ext i; simp
  rw [hs]
  simp

theorem cubicOctadOverlap (D F : Octad) :
    overlap (octadWord D).val (octadWord F).val = (D.val ∩ F.val).card := by
  rw [overlap_inter,octadWord_support,octadWord_support]

/-- The exact third-octad intersection equation for the sextet branch. -/
theorem cubicSextetCompletion_intersection_equation (D F G : Octad)
    (hFG : (F.val ∩ G.val).card = 4) :
    (D.val ∩ (cubicSextetCompletion F G hFG).val).card +
      2 * ((D.val ∩ F.val) ∩ G.val).card =
      (D.val ∩ F.val).card + (D.val ∩ G.val).card := by
  have h := parkerOverlap_add (octadWord F).val (octadWord G).val (octadWord D).val
  have hw : (octadWord F).val + (octadWord G).val =
      (octadWord (cubicSextetCompletion F G hFG)).val :=
    (congrArg Subtype.val (cubicSextetCompletion_word F G hFG)).symm
  rw [hw,cubicOctadOverlap,cubicOctadOverlap,cubicOctadOverlap,cubicOctadTripleCount] at h
  simpa only [Finset.inter_comm] using h

/-- The disjoint branch partitions all 24 coordinates into three octads. -/
theorem cubicTrioCompletion_intersection_equation (D F G : Octad)
    (hFG : (F.val ∩ G.val).card = 0) :
    (D.val ∩ (cubicTrioCompletion F G hFG).val).card +
      (D.val ∩ F.val).card + (D.val ∩ G.val).card = 8 := by
  have h := cubicTrioCompletion_intersection_sum F G D hFG
  simpa only [Finset.inter_comm,add_comm,add_left_comm,add_assoc] using h

theorem cubicSextetCompletion_refined_intersection (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 4) (hDG : (D.val ∩ G.val).card = 4)
    (hFG : (F.val ∩ G.val).card = 4) :
    (D.val ∩ (cubicSextetCompletion F G hFG).val).card =
      8 - 2 * ((D.val ∩ F.val) ∩ G.val).card := by
  have h := cubicSextetCompletion_intersection_equation D F G hFG
  rw [hDF,hDG] at h
  omega

theorem cubicTripleIntersection_zero_left (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 0) : ((D.val ∩ F.val) ∩ G.val).card = 0 := by
  rw [Finset.card_eq_zero.mp hDF,Finset.empty_inter,Finset.card_empty]

theorem cubicSextetCompletion_one_empty_intersection (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 0) (hDG : (D.val ∩ G.val).card = 4)
    (hFG : (F.val ∩ G.val).card = 4) :
    (D.val ∩ (cubicSextetCompletion F G hFG).val).card = 4 := by
  have h := cubicSextetCompletion_intersection_equation D F G hFG
  rw [hDF,hDG,cubicTripleIntersection_zero_left D F G hDF] at h
  omega

theorem cubicSextetCompletion_both_empty_intersection (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 0) (hDG : (D.val ∩ G.val).card = 0)
    (hFG : (F.val ∩ G.val).card = 4) :
    (D.val ∩ (cubicSextetCompletion F G hFG).val).card = 0 := by
  have h := cubicSextetCompletion_intersection_equation D F G hFG
  rw [hDF,hDG] at h
  omega

/-- The actual diamond's intersection size, including both admissible branches. -/
theorem cubicOctadDiamond_intersection (D F G : Octad) (hFG : OctadPairAdmissible F G) :
    (D.val ∩ (octadDiamond F G hFG).val).card =
      if (F.val ∩ G.val).card = 4 then
        (D.val ∩ F.val).card + (D.val ∩ G.val).card -
          2 * ((D.val ∩ F.val) ∩ G.val).card
      else 8 - ((D.val ∩ F.val).card + (D.val ∩ G.val).card) := by
  by_cases h4 : (F.val ∩ G.val).card = 4
  · rw [if_pos h4,octadDiamond,dif_pos h4]
    have h := cubicSextetCompletion_intersection_equation D F G h4
    omega
  · rw [if_neg h4,octadDiamond,dif_neg h4]
    have h := cubicTrioCompletion_intersection_equation D F G (hFG.resolve_left h4)
    omega

/-- Exhaustiveness of the four refined configurations follows from the actual
third octad's permitted Golay intersections. -/
theorem cubicCommonNeighbor_actual_levels (D F G : Octad)
    (hDF : (D.val ∩ F.val).card = 4) (hDG : (D.val ∩ G.val).card = 4)
    (hFG : (F.val ∩ G.val).card = 4) :
    ((D.val ∩ F.val) ∩ G.val).card = 0 ∨
    ((D.val ∩ F.val) ∩ G.val).card = 2 ∨
    ((D.val ∩ F.val) ∩ G.val).card = 3 ∨
    ((D.val ∩ F.val) ∩ G.val).card = 4 := by
  have he := cubicSextetCompletion_intersection_equation D F G hFG
  rw [hDF,hDG] at he
  have hs := octad_intersection_sizes D.val (cubicSextetCompletion F G hFG).val
    D.property (cubicSextetCompletion F G hFG).property
  omega

end Atlas.Fischer



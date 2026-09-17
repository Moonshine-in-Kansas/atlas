import Atlas.Fischer.CubicTriangleMomentSums
import Atlas.Fischer.CubicCoordinateAveraging

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicSextetIncidenceSum_diagonal (i : Omega) :
    cubicSextetIncidenceSum i i i=-1062600 := by
  have hm := cubicTriangle_family_diagonal (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.1) (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.2.1) (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.2.2) (-120)
    cubicSextetTriangle_triple_sum
  change (∑ a,cubicSextetIncidenceSum a a a)=_ at hm
  rw [cubicInvariant_diagonal_average _ cubicSextetIncidenceSum_invariant i] at hm
  rw [← Nat.card_eq_fintype_card,orderedCubicSextetTriangle_card] at hm
  norm_num at hm
  linear_combination (1/24 : Scalar)*hm

theorem cubicSextetIncidenceSum_two_equal (i j : Omega) (hij : i ≠ j) :
    cubicSextetIncidenceSum i i j=120120 := by
  have hm := cubicTriangle_family_two_equal (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.1) (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.2.1) (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.2.2) (24) (-120)
    (fun t => cubicPointOctadIncidence_sum t.val.2.2)
    cubicSextetTriangle_pair_sum cubicSextetTriangle_triple_sum
  change (∑ a,∑ b,if a ≠ b then cubicSextetIncidenceSum a a b else 0)=_ at hm
  rw [cubicInvariant_two_equal_average _ cubicSextetIncidenceSum_invariant i j hij] at hm
  rw [← Nat.card_eq_fintype_card,orderedCubicSextetTriangle_card] at hm
  norm_num at hm
  linear_combination (1/552 : Scalar)*hm

theorem cubicSextetIncidenceSum_distinct (i j k : Omega)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cubicSextetIncidenceSum i j k=-5320 := by
  have hac (t : OrderedCubicSextetTriangle) :
      (∑ i,cubicPointOctadIncidence i t.val.1*cubicPointOctadIncidence i t.val.2.2)=24 :=
    cubicSextetTriangle_pair_sum (cubicSextetSwapLast t)
  have hbc (t : OrderedCubicSextetTriangle) :
      (∑ i,cubicPointOctadIncidence i t.val.2.1*cubicPointOctadIncidence i t.val.2.2)=24 :=
    cubicSextetTriangle_pair_sum (cubicSextetSwapLast (cubicSextetSwapFirst t))
  have hm := cubicTriangle_family_distinct (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.1) (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.2.1) (fun (t : OrderedCubicSextetTriangle) i => cubicPointOctadIncidence i t.val.2.2) (24) (-120)
    (fun t => cubicPointOctadIncidence_sum t.val.1)
    (fun t => cubicPointOctadIncidence_sum t.val.2.1)
    (fun t => cubicPointOctadIncidence_sum t.val.2.2)
    cubicSextetTriangle_pair_sum hac hbc cubicSextetTriangle_triple_sum
  change (∑ a,∑ b,∑ c,if a ≠ b ∧ a ≠ c ∧ b ≠ c then cubicSextetIncidenceSum a b c else 0)=_ at hm
  rw [cubicInvariant_distinct_average _ cubicSextetIncidenceSum_invariant i j k hij hik hjk] at hm
  rw [← Nat.card_eq_fintype_card,orderedCubicSextetTriangle_card] at hm
  norm_num at hm
  linear_combination (1/12144 : Scalar)*hm

theorem cubicTrioIncidenceSum_diagonal (i : Omega) :
    cubicTrioIncidenceSum i i i=68310 := by
  have hm := cubicTriangle_family_diagonal (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.1) (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.2.1) (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.2.2) (72)
    cubicTrio_triple_sum
  change (∑ a,cubicTrioIncidenceSum a a a)=_ at hm
  rw [cubicInvariant_diagonal_average _ cubicTrioIncidenceSum_invariant i] at hm
  rw [← Nat.card_eq_fintype_card,orderedCubicTrio_card] at hm
  norm_num at hm
  linear_combination (1/24 : Scalar)*hm

theorem cubicTrioIncidenceSum_two_equal (i j : Omega) (hij : i ≠ j) :
    cubicTrioIncidenceSum i i j=-16170 := by
  have hm := cubicTriangle_family_two_equal (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.1) (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.2.1) (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.2.2) (-40) (72)
    (fun t => cubicPointOctadIncidence_sum t.val.2.2)
    cubicTrio_pair_sum cubicTrio_triple_sum
  change (∑ a,∑ b,if a ≠ b then cubicTrioIncidenceSum a a b else 0)=_ at hm
  rw [cubicInvariant_two_equal_average _ cubicTrioIncidenceSum_invariant i j hij] at hm
  rw [← Nat.card_eq_fintype_card,orderedCubicTrio_card] at hm
  norm_num at hm
  linear_combination (1/552 : Scalar)*hm

theorem cubicTrioIncidenceSum_distinct (i j k : Omega)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cubicTrioIncidenceSum i j k=3030 := by
  have hac (t : OrderedCubicTrio) :
      (∑ i,cubicPointOctadIncidence i t.val.1*cubicPointOctadIncidence i t.val.2.2)=-40 :=
    cubicTrio_pair_sum (cubicTrioSwapLast t)
  have hbc (t : OrderedCubicTrio) :
      (∑ i,cubicPointOctadIncidence i t.val.2.1*cubicPointOctadIncidence i t.val.2.2)=-40 :=
    cubicTrio_pair_sum (cubicTrioSwapLast (cubicTrioSwapFirst t))
  have hm := cubicTriangle_family_distinct (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.1) (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.2.1) (fun (t : OrderedCubicTrio) i => cubicPointOctadIncidence i t.val.2.2) (-40) (72)
    (fun t => cubicPointOctadIncidence_sum t.val.1)
    (fun t => cubicPointOctadIncidence_sum t.val.2.1)
    (fun t => cubicPointOctadIncidence_sum t.val.2.2)
    cubicTrio_pair_sum hac hbc cubicTrio_triple_sum
  change (∑ a,∑ b,∑ c,if a ≠ b ∧ a ≠ c ∧ b ≠ c then cubicTrioIncidenceSum a b c else 0)=_ at hm
  rw [cubicInvariant_distinct_average _ cubicTrioIncidenceSum_invariant i j k hij hik hjk] at hm
  rw [← Nat.card_eq_fintype_card,orderedCubicTrio_card] at hm
  norm_num at hm
  linear_combination (1/12144 : Scalar)*hm

end Atlas.Fischer

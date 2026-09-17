import Atlas.Fischer.WittDistributions

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The point-refined Witt distribution inside an actual octad. -/
theorem octad_inside_point_distribution (O : Finset Omega) (hO : O ∈ octads)
    (i : Omega) (hi : i ∈ O) :
    octadIntersectionCount O {i} 0=0 ∧ octadIntersectionCount O {i} 2=112 ∧
      octadIntersectionCount O {i} 4=140 ∧ octadIntersectionCount O {i} 8=1 := by
  have hsub : {i} ⊆ O := by simpa using hi
  have hcard := octadReplication_one {i} (by simp)
  have m0 := octad_intersection_moment_levels O {i} hO 0
  have hs : (∑ B ∈ octads.filter (fun B => {i} ⊆ B),(B ∩ O).card.choose 0)=
      octadReplication {i} := by simp [octadReplication]
  rw [hs,hcard] at m0
  norm_num at m0
  have h8 := octadIntersectionCount_eight O {i} hO
  simp only [hsub,ite_true] at h8
  have h0 : octadIntersectionCount O {i} 0=0 := by
    unfold octadIntersectionCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨_,hTB,hBI⟩ := Finset.mem_filter.mp hB
    have hc := Finset.card_le_card (Finset.subset_inter hTB hsub)
    simp only [Finset.card_singleton] at hc
    omega
  have hdiff : (O \ {i}).card=7 := by
    rw [Finset.card_sdiff_of_subset hsub,octad_size O hO]
    simp
  have m1 := octad_intersection_moment (O \ {i}) {i} 1 77 Finset.sdiff_disjoint
    (by simpa using octadReplication_two)
  norm_num [hdiff] at m1
  have he (B : Finset Omega) (hB : B ∈ octads.filter (fun B => {i} ⊆ B)) :
      (B ∩ (O \ {i})).card+1=(B ∩ O).card := by
    have hTB := (Finset.mem_filter.mp hB).2
    have hh : B ∩ (O \ {i})=(B ∩ O) \ {i} := by ext x; simp; tauto
    rw [hh,Finset.card_sdiff_of_subset (Finset.subset_inter hTB hsub)]
    have hd := Nat.sub_add_cancel (Finset.card_le_card (Finset.subset_inter hTB hsub))
    simpa only [Finset.card_singleton] using hd
  have hsum := Finset.sum_congr rfl he
  rw [Finset.sum_add_distrib] at hsum
  have mfull := octad_intersection_moment_levels O {i} hO 1
  norm_num at mfull
  have hS : (octads.filter (fun B => {i} ⊆ B)).card=253 := hcard
  simp only [Finset.sum_const,smul_eq_mul,hS,mul_one] at hsum
  simp only [Finset.singleton_subset_iff] at hsum
  omega

end Atlas.Fischer

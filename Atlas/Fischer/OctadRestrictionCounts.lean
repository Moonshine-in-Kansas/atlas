import Atlas.Fischer.WittDistributions

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Exact intersection with the marked octad, rather than only intersection size. -/
def octadRestrictionCount (O S : Finset Omega) : ℕ := by
  classical
  exact (octads.filter (fun B => B ∩ O = S)).card

theorem octadRestrictionCount_eq_intersectionCount (O S : Finset Omega) (hSO : S ⊆ O) :
    octadRestrictionCount O S = octadIntersectionCount O S S.card := by
  classical
  unfold octadRestrictionCount octadIntersectionCount
  congr 1
  ext B
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  constructor
  · intro h
    exact ⟨h ▸ Finset.inter_subset_left, congrArg Finset.card h⟩
  · rintro ⟨hSB,hcard⟩
    exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hSB hSO)
      (by omega)).symm

theorem octadRestrictionCount_duad (O S : Finset Omega) (hO : O ∈ octads)
    (hSO : S ⊆ O) (hS : S.card = 2) : octadRestrictionCount O S = 16 := by
  rw [octadRestrictionCount_eq_intersectionCount O S hSO,hS]
  exact (octad_inside_duad_distribution O S hO hSO hS).1

theorem octadRestrictionCount_tetrad (O S : Finset Omega) (hO : O ∈ octads)
    (hSO : S ⊆ O) (hS : S.card = 4) : octadRestrictionCount O S = 4 := by
  classical
  rw [octadRestrictionCount_eq_intersectionCount O S hSO,hS]
  have m0 := octad_intersection_moment_levels O S hO 0
  have hs : (∑ B ∈ octads.filter (fun B => S ⊆ B), (B ∩ O).card.choose 0) =
      octadReplication S := by simp [octadReplication]
  rw [hs,octadReplication_four S hS] at m0
  norm_num at m0
  have h8 := octadIntersectionCount_eight O S hO
  simp only [hSO,ite_true] at h8
  have hz (j : ℕ) (hj : j < 4) : octadIntersectionCount O S j = 0 := by
    unfold octadIntersectionCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨_,hSB,hBI⟩ := Finset.mem_filter.mp hB
    have hc := Finset.card_le_card (Finset.subset_inter hSB hSO)
    omega
  have h0 := hz 0 (by omega)
  have h2 := hz 2 (by omega)
  omega

theorem octadRestrictionCount_six (O S : Finset Omega) (hO : O ∈ octads)
    (hS : S.card = 6) : octadRestrictionCount O S = 0 := by
  classical
  unfold octadRestrictionCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro B hB
  obtain ⟨hB,hBS⟩ := Finset.mem_filter.mp hB
  have hc := octad_intersection_sizes B O hB hO
  rw [hBS,hS] at hc
  omega

theorem octadRestrictionCount_empty (O : Finset Omega) (hO : O ∈ octads) :
    octadRestrictionCount O ∅ = 30 := by
  rw [octadRestrictionCount_eq_intersectionCount O ∅ (Finset.empty_subset O)]
  exact (octad_intersection_distribution O hO).1

theorem octadRestrictionCount_self (O : Finset Omega) (hO : O ∈ octads) :
    octadRestrictionCount O O = 1 := by
  rw [octadRestrictionCount_eq_intersectionCount O O (Finset.Subset.refl O),
    octad_size O hO,octadIntersectionCount_eight O O hO]
  simp

end Atlas.Fischer

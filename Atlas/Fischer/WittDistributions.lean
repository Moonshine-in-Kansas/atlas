import Atlas.Fischer.WittIntersectionMoments
import Atlas.Combinatorics.FourLevelMoments
import Atlas.Mathieu.HeptadIntersections

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Combinatorics
open scoped BigOperators

def octadIntersectionCount (O T : Finset Omega) (j : ℕ) : ℕ := by
  classical
  exact (octads.filter (fun B => T ⊆ B ∧ (B ∩ O).card = j)).card

theorem octad_intersection_moment_levels (O T : Finset Omega) (hO : O ∈ octads) (k : ℕ) :
    (∑ B ∈ octads.filter (fun B => T ⊆ B), (B ∩ O).card.choose k) =
      Nat.choose 0 k * octadIntersectionCount O T 0 +
      Nat.choose 2 k * octadIntersectionCount O T 2 +
      Nat.choose 4 k * octadIntersectionCount O T 4 +
      Nat.choose 8 k * octadIntersectionCount O T 8 := by
  classical
  have h := four_level_sum (octads.filter (fun B => T ⊆ B))
    (fun B => (B ∩ O).card) (fun B => (B ∩ O).card.choose k)
    0 2 4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun n => n.choose k)
    (fun B hB => octad_intersection_sizes B O (Finset.mem_filter.mp hB).1 hO)
    (fun _ _ => rfl)
  simpa only [octadIntersectionCount,Finset.filter_filter] using h

theorem octadIntersectionCount_eight (O T : Finset Omega) (hO : O ∈ octads) :
    octadIntersectionCount O T 8 = if T ⊆ O then 1 else 0 := by
  classical
  have he (B : Finset Omega) (hB : B ∈ octads) : (B ∩ O).card = 8 ↔ B = O := by
    constructor
    · intro hc
      have hBO : B ∩ O = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by rw [octad_size B hB,hc])
      exact Finset.eq_of_subset_of_card_le (Finset.inter_eq_left.mp hBO)
        (by rw [octad_size O hO,octad_size B hB])
    · intro h
      subst B
      simpa using octad_size O hO
  have hf : octads.filter (fun B => T ⊆ B ∧ (B ∩ O).card = 8) =
      if T ⊆ O then {O} else ∅ := by
    ext B
    by_cases hTO : T ⊆ O
    · simp only [hTO,ite_true,Finset.mem_filter,Finset.mem_singleton]
      constructor
      · intro h
        exact (he B h.1).mp h.2.2
      · intro h
        subst B
        exact ⟨hO,hTO,(he O hO).mpr rfl⟩
    · simp only [hTO,ite_false,Finset.mem_filter,Finset.notMem_empty,iff_false]
      rintro ⟨hB,hTB,hcard⟩
      exact hTO ((he B hB).mp hcard ▸ hTB)
  unfold octadIntersectionCount
  rw [hf]
  split_ifs <;> simp

/-- The three binomial moments of any outside-set section of the Witt design. -/
theorem octad_distribution_equations (O T : Finset Omega) (hO : O ∈ octads)
    (hOT : Disjoint O T) (l0 l1 l2 : ℕ)
    (h0 : ∀ U : Finset Omega, U.card = T.card → octadReplication U = l0)
    (h1 : ∀ U : Finset Omega, U.card = T.card+1 → octadReplication U = l1)
    (h2 : ∀ U : Finset Omega, U.card = T.card+2 → octadReplication U = l2) :
    octadIntersectionCount O T 0 + octadIntersectionCount O T 2 +
      octadIntersectionCount O T 4 + octadIntersectionCount O T 8 = l0 ∧
    2*octadIntersectionCount O T 2 + 4*octadIntersectionCount O T 4 +
      8*octadIntersectionCount O T 8 = 8*l1 ∧
    octadIntersectionCount O T 2 + 6*octadIntersectionCount O T 4 +
      28*octadIntersectionCount O T 8 = 28*l2 := by
  have m0 := octad_intersection_moment O T 0 l0 hOT (by simpa using h0)
  have m1 := octad_intersection_moment O T 1 l1 hOT h1
  have m2 := octad_intersection_moment O T 2 l2 hOT h2
  rw [octad_intersection_moment_levels O T hO,octad_size O hO] at m0 m1 m2
  norm_num [Nat.choose] at m0 m1 m2
  exact ⟨m0,m1,m2⟩

theorem octad_intersection_distribution (O : Finset Omega) (hO : O ∈ octads) :
    octadIntersectionCount O ∅ 0 = 30 ∧ octadIntersectionCount O ∅ 2 = 448 ∧
    octadIntersectionCount O ∅ 4 = 280 ∧ octadIntersectionCount O ∅ 8 = 1 := by
  have h := octad_distribution_equations O ∅ hO (by simp) 759 253 77
    (by simpa using octadReplication_zero)
    (by simpa using octadReplication_one)
    (by simpa using octadReplication_two)
  have h8 := octadIntersectionCount_eight O ∅ hO
  simp only [Finset.empty_subset,ite_true] at h8
  omega

private theorem outside_eight_zero (O T : Finset Omega) (hO : O ∈ octads)
    (hOT : Disjoint O T) (hT : T.Nonempty) : octadIntersectionCount O T 8 = 0 := by
  rw [octadIntersectionCount_eight O T hO]
  have hn : ¬ T ⊆ O := by
    intro h
    obtain ⟨x,hx⟩ := hT
    exact Finset.disjoint_left.mp hOT (h hx) hx
  simp [hn]

theorem octad_outside_point_distribution (O T : Finset Omega) (hO : O ∈ octads)
    (hOT : Disjoint O T) (hT : T.card = 1) :
    octadIntersectionCount O T 0 = 15 ∧ octadIntersectionCount O T 2 = 168 ∧
    octadIntersectionCount O T 4 = 70 := by
  have h := octad_distribution_equations O T hO hOT 253 77 21
    (by simpa [hT] using octadReplication_one)
    (by simpa [hT] using octadReplication_two)
    (by simpa [hT] using octadReplication_three)
  have h8 := outside_eight_zero O T hO hOT (Finset.card_pos.mp (by omega))
  omega

theorem octad_outside_duad_distribution (O T : Finset Omega) (hO : O ∈ octads)
    (hOT : Disjoint O T) (hT : T.card = 2) :
    octadIntersectionCount O T 0 = 7 ∧ octadIntersectionCount O T 2 = 56 ∧
    octadIntersectionCount O T 4 = 14 := by
  have h := octad_distribution_equations O T hO hOT 77 21 5
    (by simpa [hT] using octadReplication_two)
    (by simpa [hT] using octadReplication_three)
    (by simpa [hT] using octadReplication_four)
  have h8 := outside_eight_zero O T hO hOT (Finset.card_pos.mp (by omega))
  omega

/-- Incidence with the six points of an octad outside a contained duad. -/
theorem octad_inside_duad_distribution (O T : Finset Omega) (hO : O ∈ octads)
    (hTO : T ⊆ O) (hT : T.card = 2) :
    octadIntersectionCount O T 2 = 16 ∧ octadIntersectionCount O T 4 = 60 := by
  classical
  have hcard := octadReplication_two T hT
  have m0 := octad_intersection_moment_levels O T hO 0
  have hs : (∑ B ∈ octads.filter (fun B => T ⊆ B), (B ∩ O).card.choose 0) =
      octadReplication T := by simp [octadReplication]
  rw [hs,hcard] at m0
  norm_num at m0
  have h8 := octadIntersectionCount_eight O T hO
  simp only [hTO,ite_true] at h8
  have hzero : octadIntersectionCount O T 0 = 0 := by
    unfold octadIntersectionCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨_,hTB,hBI⟩ := Finset.mem_filter.mp hB
    have hc := Finset.card_le_card (Finset.subset_inter hTB hTO)
    omega
  have hOT : Disjoint (O \ T) T := Finset.sdiff_disjoint
  have hdiff : (O \ T).card = 6 := by
    rw [Finset.card_sdiff_of_subset hTO,octad_size O hO,hT]
  have m1 := octad_intersection_moment (O \ T) T 1 21 hOT
    (by simpa [hT] using octadReplication_three)
  norm_num [hdiff] at m1
  have he (B : Finset Omega) (hB : B ∈ octads.filter (fun B => T ⊆ B)) :
      (B ∩ (O \ T)).card + 2 = (B ∩ O).card := by
    have hTB := (Finset.mem_filter.mp hB).2
    have hh : B ∩ (O \ T) = (B ∩ O) \ T := by ext x; simp; tauto
    rw [hh,Finset.card_sdiff_of_subset (Finset.subset_inter hTB hTO)]
    have hd := Nat.sub_add_cancel (Finset.card_le_card (Finset.subset_inter hTB hTO))
    simpa only [hT] using hd
  have hsum := Finset.sum_congr rfl he
  rw [Finset.sum_add_distrib] at hsum
  have mfull := octad_intersection_moment_levels O T hO 1
  norm_num at mfull
  have hS : (octads.filter (fun B => T ⊆ B)).card = 77 := hcard
  simp only [Finset.sum_const,smul_eq_mul,hS] at hsum
  rw [m1, mfull] at hsum
  omega

end Atlas.Fischer

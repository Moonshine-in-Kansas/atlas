import Atlas.Fischer.WittDistributions

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- First two incidence equations when exactly one prescribed point lies in O. -/
theorem octad_one_inside_equations (O T : Finset Omega) (hO : O ∈ octads)
    (i : Omega) (hiO : i ∈ O) (hiT : i ∈ T) (hOT : Disjoint (O \ {i}) T)
    (l0 l1 : ℕ) (h0 : octadReplication T = l0)
    (h1 : ∀ U : Finset Omega, U.card = T.card + 1 → octadReplication U = l1) :
    octadIntersectionCount O T 2 + octadIntersectionCount O T 4 +
      octadIntersectionCount O T 8 = l0 ∧
    2 * octadIntersectionCount O T 2 + 4 * octadIntersectionCount O T 4 +
      8 * octadIntersectionCount O T 8 = 7 * l1 + l0 := by
  classical
  have m0 := octad_intersection_moment_levels O T hO 0
  have hs : (∑ B ∈ octads.filter (fun B => T ⊆ B), (B ∩ O).card.choose 0) =
      octadReplication T := by simp [octadReplication]
  rw [hs, h0] at m0
  norm_num at m0
  have hz : octadIntersectionCount O T 0 = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨_, hTB, hc⟩ := Finset.mem_filter.mp hB
    have hm : i ∈ B ∩ O := Finset.mem_inter.mpr ⟨hTB hiT, hiO⟩
    have hp := Finset.card_pos.mpr ⟨i, hm⟩
    omega
  have hdiff : (O \ {i}).card = 7 := by
    rw [Finset.card_sdiff_of_subset (by simpa using hiO), octad_size O hO]
    simp
  have m1 := octad_intersection_moment (O \ {i}) T 1 l1 hOT h1
  norm_num [hdiff] at m1
  have he (B : Finset Omega) (hB : B ∈ octads.filter (fun B => T ⊆ B)) :
      (B ∩ (O \ {i})).card + 1 = (B ∩ O).card := by
    have hiB := (Finset.mem_filter.mp hB).2 hiT
    have hh : B ∩ (O \ {i}) = (B ∩ O) \ {i} := by ext x; simp; tauto
    have hsub : {i} ⊆ B ∩ O := by simp [hiB, hiO]
    rw [hh, Finset.card_sdiff_of_subset hsub]
    simpa only [Finset.card_singleton] using Nat.sub_add_cancel (Finset.card_le_card hsub)
  have hsum := Finset.sum_congr rfl he
  rw [Finset.sum_add_distrib] at hsum
  have mf := octad_intersection_moment_levels O T hO 1
  norm_num at mf
  have hc : (octads.filter (fun B => T ⊆ B)).card = l0 := h0
  simp only [Finset.sum_const, smul_eq_mul, hc, mul_one] at hsum
  rw [m1, mf] at hsum
  omega

theorem octad_inside_point_four (O : Octad) (i : Omega) (hi : i ∈ O.val) :
    octadIntersectionCount O.val {i} 4 = 140 := by
  classical
  have he := octad_one_inside_equations O.val {i} O.property i hi (by simp)
    Finset.sdiff_disjoint 253 77 (octadReplication_one _ (by simp))
    (by simpa using octadReplication_two)
  have h8 := octadIntersectionCount_eight O.val {i} O.property
  simp only [Finset.singleton_subset_iff, hi, ite_true] at h8
  omega

theorem octad_inside_outside_pair_four (O : Octad) (i j : Omega)
    (hi : i ∈ O.val) (hj : j ∉ O.val) :
    octadIntersectionCount O.val {i, j} 4 = 35 := by
  classical
  have hij : i ≠ j := by intro h; exact hj (h ▸ hi)
  have hd : Disjoint (O.val \ {i}) {i, j} := by
    apply Finset.disjoint_left.mpr
    intro x hx ht
    obtain ⟨hxO, hxi⟩ := Finset.mem_sdiff.mp hx
    rcases Finset.mem_insert.mp ht with he | he
    · subst x
      exact hxi (by simp)
    · have hxj := Finset.mem_singleton.mp he
      subst x
      exact hj hxO
  have hc : ({i, j} : Finset Omega).card = 2 := by simp [hij]
  have he := octad_one_inside_equations O.val {i, j} O.property i hi (by simp)
    hd 77 21 (octadReplication_two _ hc) (by simpa [hc] using octadReplication_three)
  have h8 := octadIntersectionCount_eight O.val {i, j} O.property
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj, and_false, ite_false] at h8
  omega

end Atlas.Fischer

import Atlas.Fischer.WittDistributions

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Combinatorics

/-- Actual intersection moment after removing already marked interior points. -/
theorem octad_marked_remainder_levels (O : Octad) (S T : Finset Omega)
    (hSO : S ⊆ O.val) (hST : S ⊆ T) :
    (∑ B ∈ octads.filter (fun B => T ⊆ B), (B ∩ (O.val \ S)).card)=
      (0-S.card)*octadIntersectionCount O.val T 0+
      (2-S.card)*octadIntersectionCount O.val T 2+
      (4-S.card)*octadIntersectionCount O.val T 4+
      (8-S.card)*octadIntersectionCount O.val T 8 := by
  classical
  have h := four_level_sum (octads.filter (fun B => T ⊆ B))
    (fun B => (B ∩ O.val).card) (fun B => (B ∩ (O.val \ S)).card)
    0 2 4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun j => j-S.card)
    (fun B hB => octad_intersection_sizes B O.val (Finset.mem_filter.mp hB).1 O.prop) (by
      intro B hB
      have hSB : S ⊆ B ∩ O.val := Finset.subset_inter
        (hST.trans (Finset.mem_filter.mp hB).2) hSO
      have he : B ∩ (O.val \ S)=(B ∩ O.val) \ S := by ext i;simp;tauto
      rw [he,Finset.card_sdiff_of_subset hSB])
  simpa only [octadIntersectionCount,Finset.filter_filter] using h

/-- Two exact incidence equations for an exterior point together with nonempty
prescribed interior markings. No transitivity or target group data enter. -/
theorem octad_marked_outside_equations (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hne : S.Nonempty) (x : Omega) (hx : x ∉ O.val)
    (l0 l1 : ℕ)
    (h0 : ∀ U : Finset Omega,U.card=S.card+1 → octadReplication U=l0)
    (h1 : ∀ U : Finset Omega,U.card=S.card+2 → octadReplication U=l1) :
    octadIntersectionCount O.val (insert x S) 2+octadIntersectionCount O.val (insert x S) 4=l0 ∧
    (2-S.card)*octadIntersectionCount O.val (insert x S) 2+
      (4-S.card)*octadIntersectionCount O.val (insert x S) 4=(8-S.card)*l1 := by
  classical
  have hxS : x∉S := fun h => hx (hSO h)
  have hT : (insert x S).card=S.card+1 := Finset.card_insert_of_notMem hxS
  have h8 : octadIntersectionCount O.val (insert x S) 8=0 := by
    rw [octadIntersectionCount_eight O.val _ O.prop,if_neg]
    intro h
    exact hx (h (Finset.mem_insert_self _ _))
  have hz : octadIntersectionCount O.val (insert x S) 0=0 := by
    unfold octadIntersectionCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨hB,hTB,hc⟩ := Finset.mem_filter.mp hB
    obtain ⟨i,hi⟩ := hne
    have hm : i∈B∩O.val := Finset.mem_inter.mpr
      ⟨hTB (Finset.mem_insert_of_mem hi),hSO hi⟩
    rw [Finset.card_eq_zero.mp hc] at hm
    exact Finset.notMem_empty _ hm
  have m0 := octad_intersection_moment_levels O.val (insert x S) O.prop 0
  have hs : (∑ B ∈ octads.filter (fun B => insert x S ⊆ B), (B∩O.val).card.choose 0)=l0 := by
    simpa [octadReplication] using h0 (insert x S) hT
  rw [hs,hz,h8] at m0
  norm_num at m0
  have hd : Disjoint (O.val \ S) (insert x S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨hiO,hiS⟩ := Finset.mem_sdiff.mp hi
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hx hiO
    · exact hiS hj
  have m1 := octad_intersection_moment (O.val \ S) (insert x S) 1 l1 hd (by
    intro U hU
    exact h1 U (by omega))
  simp only [Nat.choose_one_right] at m1
  rw [octad_marked_remainder_levels O S (insert x S) hSO (Finset.subset_insert _ _),
    hz,h8,Finset.card_sdiff_of_subset hSO,octad_size O.val O.prop] at m1
  norm_num at m1
  exact ⟨m0.symm,m1⟩

end Atlas.Fischer

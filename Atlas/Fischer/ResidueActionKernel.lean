import Atlas.Fischer.ResidueKernelDuads

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Exact residue-action kernel, on the original distinguished point set. -/
theorem residueConjugationHom_kernel (S : Finset Omega) (hS : S.card ≤ 2) :
    (residueConjugationHom S).ker = residueCentralElementary S := by
  classical
  apply le_antisymm _ (residueElementary_le_action_kernel S)
  intro g hg
  by_cases h0 : S.card=0
  · have he : S=∅ := Finset.card_eq_zero.mp h0
    subst S
    have he : g.val=1 := by
      apply rootGeneratedRayGroup_central_eq_one
      intro t
      let x : ResiduePoint ∅ := ⟨distinguishedRootElement t,⟨t,rfl⟩,
        by simp [residueBasicSet],by simp⟩
      have hh := (mem_residueAction_kernel_iff ∅ g).mp hg x
      have hc := congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp hh)
      exact hc
    change g.val ∈ residueElementary ∅
    rw [he]
    exact (residueElementary ∅).one_mem
  obtain ⟨d,hd⟩ := residueAction_kernel_cocode S g hg
  change g.val ∈ residueElementary S
  rw [hd,generatedCocodeRayHom_mem_residueElementary]
  by_cases h2 : S.card=2
  · exact residueAction_kernel_duad_span S g hg d hd ⟨S,h2⟩ (Finset.Subset.refl _)
  have h1 : S.card=1 := by omega
  obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
  obtain ⟨j,hji⟩ := exists_ne i
  have hk : ∃ k : Omega, k≠i ∧ k≠j := by
    by_contra hn
    push_neg at hn
    have hsub : (Finset.univ : Finset Omega) ⊆ {i,j} := by
      intro k _
      by_cases hki : k=i
      · simp [hki]
      · simp [hn k hki]
    have hc := Finset.card_le_card hsub
    have hcard : ({i,j} : Finset Omega).card=2 := by simp [hji.symm]
    rw [Finset.card_univ,hcard] at hc
    change 24 ≤ 2 at hc
    omega
  obtain ⟨k,hki,hkj⟩ := hk
  have hjspan := residueAction_kernel_duad_span {i} g hg d hd
    ⟨{i,j},by simp [hji.symm]⟩ (by simp)
  have hkspan := residueAction_kernel_duad_span {i} g hg d hd
    ⟨{i,k},by simp [hki.symm]⟩ (by simp)
  rw [← coordinateCocodeSpan_pair_inter_pair i j k hji.symm hki.symm hkj.symm]
  exact ⟨hjspan,hkspan⟩

end Atlas.Fischer

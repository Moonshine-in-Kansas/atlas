import Atlas.Lattices.EisensteinNormalizedShortCodes

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

/-- A normalized constant-hexad norm-six vector has exactly one excess norm-three
coordinate: either a heavy coordinate on the hexad or a norm-nine coordinate outside it. -/
theorem eisenstein_constant_normalized_norm_pattern (s : Finset (Fin 12)) (hs : s.card=6)
    (x : EisensteinShell 6) (u : EisensteinCoordinates) (hu : x.val.val=eisensteinTheta • u)
    (hr : eisensteinWordResidue u=ternaryTriadWord s) :
    ∃ k : Fin 12,∀ i,(u i).norm=(if i ∈ s then 1 else 0)+(if i=k then 3 else 0) := by
  classical
  let d : Fin 12 → ℤ := fun i => (u i).norm-(if i ∈ s then 1 else 0)
  have hres (i : Fin 12) : eisensteinResidue (u i)=if i ∈ s then 1 else 0 := by
    exact congrFun hr i
  have hd0 (i : Fin 12) : 0≤d i := by
    have hn := eisenstein_norm_nonneg (u i)
    by_cases hi : i ∈ s
    · have hn0 : (u i).norm≠0 := by
        intro h
        have he := eisensteinResidue_norm (u i)
        rw [h,hres,if_pos hi] at he
        norm_num at he
      dsimp [d]; rw [if_pos hi]; omega
    · simpa [d,hi] using hn
  have hd3 (i : Fin 12) : (3 : ℤ) ∣ d i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (d i) 3).mp
    dsimp [d]
    push_cast
    rw [eisensteinResidue_norm,hres]
    by_cases hi : i ∈ s <;> simp [hi]
  have hsum : ∑ i,d i=3 := by
    simp only [d,Finset.sum_sub_distrib]
    rw [eisenstein_six_normalized_norm_sum x u hu]
    norm_num [hs]
  obtain ⟨k,hk⟩ : ∃ k,d k≠0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  have hkle : d k≤3 := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 12))) => hd0 i)
      (Finset.mem_univ k)
    simpa [hsum] using h
  have hk3 : d k=3 := by
    obtain ⟨a,ha⟩ := hd3 k
    have h := hd0 k
    omega
  have herase : ∑ i ∈ (Finset.univ.erase k),d i=0 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin 12)) d (Finset.mem_univ k)
    rw [hsum,hk3] at h
    omega
  have hrest (i : Fin 12) (hi : i≠k) : d i=0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd0 j)).mp herase i
      (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩)
  refine ⟨k,fun i => ?_⟩
  by_cases hi : i=k
  · subst i
    dsimp [d] at hk3
    rw [if_pos rfl]
    omega
  · have h := hrest i hi
    dsimp [d] at h
    rw [if_neg hi]
    omega

end Atlas.Lattices

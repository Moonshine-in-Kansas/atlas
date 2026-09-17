import Atlas.Conway.EisensteinConstantFramePattern
import Atlas.Conway.EisensteinConstantNineInjective

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

private theorem constantNine_norm_zero (z : Eisenstein) (h : z.norm=0) : z=0 := by
  rw [eisenstein_norm] at h
  have hr : z.re=0 := by nlinarith [sq_nonneg z.im,sq_nonneg (z.re-z.im)]
  have hi : z.im=0 := by nlinarith [sq_nonneg z.re,sq_nonneg (z.re-z.im)]
  exact QuadraticAlgebra.ext hr hi

/-- The six actual integral units split into the two nonzero correction signs and three phases. -/
theorem eisensteinUnit_correction_phase (a : Eisensteinˣ) :
    ∃ b : ZMod 3,b≠0 ∧ ∃ z : ZMod 3,(a : Eisenstein)= -eisensteinPhaseCorrection b*eisensteinPhase z := by
  have hn := (eisenstein_isUnit_iff (a : Eisenstein)).mp a.isUnit
  rcases (eisenstein_norm_one_iff (a : Eisenstein)).mp hn with h|h|h|h|h|h
  all_goals rw [h]; decide +kernel

/-- Raw coordinate normal form for every positively normalized constant norm-nine vector. -/
theorem eisensteinConstantNine_normal_form (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k : Fin 12) (hk : k ∉ s)
    (u : EisensteinCoordinates) (hr : eisensteinWordResidue u=ternaryTriadWord s)
    (hn : ∀ i,(u i).norm=(if i ∈ s then 1 else 0)+(if i=k then 3 else 0))
    (hu : eisensteinTheta • u ∈ eisensteinLeechModule) :
    ∃ b : ZMod 3,b≠0 ∧ ∃ z : ZMod 3,∃ t : TernaryWord,
      (∑ i ∈ s,t i)=b ∧ ∀ i,u i=(if i ∈ s then eisensteinPhase (t i) else 0)-
        if i=k then eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase z else 0 := by
  have hk3 : (u k).norm=3 := by simpa [hk] using hn k
  obtain ⟨a,ha⟩ := eisenstein_norm_three_unit (u k) hk3
  obtain ⟨b,hb,z,hz⟩ := eisensteinUnit_correction_phase a
  have ht (i : Fin 12) : ∃ t : ZMod 3,i ∈ s → u i=eisensteinPhase t := by
    by_cases hi : i ∈ s
    · have hik : i≠k := by intro h; exact hk (h ▸ hi)
      have h1 : (u i).norm=1 := by simpa [hi,hik] using hn i
      have hri : eisensteinResidue (u i)=1 := by
        have h := congrFun hr i
        simpa [eisensteinWordResidue,ternaryTriadWord,hi] using h
      obtain ⟨t,ht⟩ := eisensteinUnit_residue_one_phase (u i) ((eisenstein_isUnit_iff _).mpr h1) hri
      exact ⟨t,fun _ => ht⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose t ht using ht
  have he (i : Fin 12) : u i=(if i ∈ s then eisensteinPhase (t i) else 0)-
      if i=k then eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase z else 0 := by
    by_cases hi : i ∈ s
    · have hik : i≠k := by intro h; exact hk (h ▸ hi)
      simp [hi,hik,ht i hi]
    · by_cases hik : i=k
      · subst i
        rw [ha,hz]
        simp [hk]
        ring
      · have h0 : (u i).norm=0 := by simpa [hi,hik] using hn i
        simp [hi,hik,constantNine_norm_zero _ h0]
  have hsum : ∑ i ∈ s,t i=b := by
    let Z : Eisenstein := (∑ i ∈ s,eisensteinPhaseCorrection (t i))-
      eisensteinPhaseCorrection b*eisensteinPhase z
    have huSum : ∑ i,u i=6+eisensteinTheta*Z := by
      simp_rw [he]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      simp_rw [eisensteinPhase_correction]
      simp only [Finset.sum_add_distrib,Finset.sum_const,← Finset.mul_sum,nsmul_eq_mul,mul_one]
      rw [((mem_ternaryConstantHexads _).mp hs).1]
      dsimp [Z]
      rw [eisensteinPhase_correction]
      ring
    have hdiv := ((eisensteinLeechModule_theta_iff u).mp hu).2
    have hd : (3 : Eisenstein) ∣ eisensteinTheta*Z := by
      have h := dvd_sub hdiv (show (3 : Eisenstein) ∣ 6 from ⟨2,by norm_num⟩)
      simpa [huSum] using h
    have hrZ := (eisensteinResidue_eq_zero Z).mpr ((eisenstein_three_dvd_theta_iff Z).mp hd)
    simp only [Z,map_sub,map_sum,map_mul,eisensteinPhaseCorrection_residue,
      eisensteinPhase_residue,mul_one,Finset.sum_neg_distrib] at hrZ
    linear_combination -hrZ
  exact ⟨b,hb,z,t,hsum,he⟩

end Atlas.Conway

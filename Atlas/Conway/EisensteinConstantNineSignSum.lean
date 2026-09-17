import Atlas.Lattices.EisensteinConstantHexadSum
import Atlas.Lattices.EisensteinPhases

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

def eisensteinConstantNineForm (s : Finset (Fin 12)) (k : Fin 12) (b z : ZMod 3)
    (t : TernaryWord) : EisensteinCoordinates := fun i =>
  (if i ∈ s then eisensteinPhase (t i) else 0)-
    if i=k then eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase z else 0

theorem eisensteinConstantNineForm_hexad_sum (s : Finset (Fin 12))
    (hs : s.card=6) (k : Fin 12) (hk : k ∉ s) (b z : ZMod 3) (t : TernaryWord) :
    (∑ i ∈ s,eisensteinConstantNineForm s k b z t i)=
      6+eisensteinTheta*(∑ i ∈ s,eisensteinPhaseCorrection (t i)) := by
  have he (i : Fin 12) (hi : i ∈ s) : eisensteinConstantNineForm s k b z t i=eisensteinPhase (t i) := by
    have hik : i≠k := by intro h; exact hk (h ▸ hi)
    simp [eisensteinConstantNineForm,hi,hik]
  rw [Finset.sum_congr rfl he]
  simp_rw [eisensteinPhase_correction]
  simp [Finset.sum_add_distrib,← Finset.mul_sum,hs]

theorem eisensteinConstantNineForm_compl_sum (s : Finset (Fin 12))
    (k : Fin 12) (hk : k ∈ s) (b z : ZMod 3) (t : TernaryWord) :
    (∑ i ∈ s,eisensteinConstantNineForm sᶜ k b z t i)=
      -eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase z := by
  have he (i : Fin 12) (hi : i ∈ s) : eisensteinConstantNineForm sᶜ k b z t i=
      -(if i=k then eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase z else 0) := by
    simp [eisensteinConstantNineForm,hi]
  rw [Finset.sum_congr rfl he]
  simp [Finset.sum_neg_distrib,hk]

/-- Same-support class cancellation preserves the actual correction sign. -/
theorem eisensteinConstantNine_sign_sub (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k l : Fin 12) (hk : k ∉ s) (hl : l ∉ s)
    (b d z w : ZMod 3) (t v : TernaryWord) (ht : (∑ i ∈ s,t i)=b) (hv : (∑ i ∈ s,v i)=d)
    (hm : eisensteinConstantNineForm s k b z t-eisensteinConstantNineForm s l d w v ∈ eisensteinLeechModule) :
    b=d := by
  have h := eisensteinLeech_constant_hexad_sum s hs _ hm
  simp only [Pi.sub_apply,Finset.sum_sub_distrib] at h
  rw [eisensteinConstantNineForm_hexad_sum s ((mem_ternaryConstantHexads s).mp hs).1 k hk,
    eisensteinConstantNineForm_hexad_sum s ((mem_ternaryConstantHexads s).mp hs).1 l hl] at h
  have he : (6+eisensteinTheta*(∑ i ∈ s,eisensteinPhaseCorrection (t i)))-
      (6+eisensteinTheta*(∑ i ∈ s,eisensteinPhaseCorrection (v i)))=
      eisensteinTheta*((∑ i ∈ s,eisensteinPhaseCorrection (t i))-
        (∑ i ∈ s,eisensteinPhaseCorrection (v i))) := by ring
  rw [he,eisenstein_three_dvd_theta_iff,← eisensteinResidue_eq_zero] at h
  simp only [map_sub,map_sum,eisensteinPhaseCorrection_residue,Finset.sum_neg_distrib,ht,hv] at h
  linear_combination -h

/-- Opposite-class cancellation on complementary supports preserves the same sign. -/
theorem eisensteinConstantNine_sign_add_compl (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k l : Fin 12) (hk : k ∉ s) (hl : l ∈ s)
    (b d z w : ZMod 3) (t v : TernaryWord) (ht : (∑ i ∈ s,t i)=b)
    (hm : eisensteinConstantNineForm s k b z t+eisensteinConstantNineForm sᶜ l d w v ∈ eisensteinLeechModule) :
    b=d := by
  have h := eisensteinLeech_constant_hexad_sum s hs _ hm
  simp only [Pi.add_apply,Finset.sum_add_distrib] at h
  rw [eisensteinConstantNineForm_hexad_sum s ((mem_ternaryConstantHexads s).mp hs).1 k hk,
    eisensteinConstantNineForm_compl_sum s l hl] at h
  have hd := dvd_sub h (show (3 : Eisenstein) ∣ 6 from ⟨2,by norm_num⟩)
  have he : 6+eisensteinTheta*(∑ i ∈ s,eisensteinPhaseCorrection (t i))+
      -eisensteinTheta*eisensteinPhaseCorrection d*eisensteinPhase w-6=
      eisensteinTheta*((∑ i ∈ s,eisensteinPhaseCorrection (t i))-
        eisensteinPhaseCorrection d*eisensteinPhase w) := by ring
  rw [he,eisenstein_three_dvd_theta_iff,← eisensteinResidue_eq_zero] at hd
  simp only [map_sub,map_sum,map_mul,eisensteinPhaseCorrection_residue,eisensteinPhase_residue,
    mul_one,Finset.sum_neg_distrib,ht] at hd
  linear_combination -hd

end Atlas.Conway

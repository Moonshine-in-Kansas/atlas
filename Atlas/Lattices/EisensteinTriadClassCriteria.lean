import Atlas.Lattices.EisensteinTriadPhases
import Atlas.Lattices.EisensteinClassCoordinates

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

def eisensteinTriadUnits (s : Finset (Fin 12)) (a : TernaryWord) : EisensteinCoordinates :=
  fun i => if i ∈ s then eisensteinPhase (a i) else 0

theorem eisensteinTriadUnits_residue (s : Finset (Fin 12)) (a : TernaryWord) :
    eisensteinWordResidue (eisensteinTriadUnits s a) = ternaryTriadWord s := by
  ext i
  by_cases hi : i ∈ s <;> simp [eisensteinWordResidue,eisensteinTriadUnits,ternaryTriadWord,hi]

theorem eisensteinTriadUnits_sum (s : Finset (Fin 12)) (hs : s.card=3) (a : TernaryWord) :
    ∑ i,eisensteinTriadUnits s a i =
      3+eisensteinTheta*(∑ i ∈ s,eisensteinPhaseCorrection (a i)) := by
  simp only [eisensteinTriadUnits,Finset.sum_ite_mem,Finset.univ_inter]
  simp_rw [eisensteinPhase_correction]
  simp [Finset.sum_add_distrib,← Finset.mul_sum,hs]

theorem eisensteinTriadUnits_difference_dvd (s t : Finset (Fin 12))
    (hs : s.card=3) (ht : t.card=3) (a b : TernaryWord) :
    (3 : Eisenstein) ∣ ∑ i,(eisensteinTriadUnits s a-eisensteinTriadUnits t b) i ↔
      ∑ i ∈ s,a i = ∑ i ∈ t,b i := by
  simp only [Pi.sub_apply,Finset.sum_sub_distrib,eisensteinTriadUnits_sum s hs a,
    eisensteinTriadUnits_sum t ht b]
  rw [show (3+eisensteinTheta*(∑ i ∈ s,eisensteinPhaseCorrection (a i))) -
      (3+eisensteinTheta*(∑ i ∈ t,eisensteinPhaseCorrection (b i))) =
      eisensteinTheta*((∑ i ∈ s,eisensteinPhaseCorrection (a i))-
        (∑ i ∈ t,eisensteinPhaseCorrection (b i))) by ring]
  rw [eisenstein_three_dvd_theta_iff,← eisensteinResidue_eq_zero]
  simp only [map_sub,map_sum,eisensteinPhaseCorrection_residue,Finset.sum_neg_distrib]
  rw [sub_eq_zero,neg_inj]

theorem eisensteinTriadClass_eq_iff (s t : Finset (Fin 12))
    (hs : s.card=3) (ht : t.card=3) (a b : TernaryWord) :
    eisensteinClass (eisensteinTriadLatticeVector s hs a) =
      eisensteinClass (eisensteinTriadLatticeVector t ht b) ↔
    ternaryTriadWord s-ternaryTriadWord t ∈ ternaryGolay ∧
      ∑ i ∈ s,a i = ∑ i ∈ t,b i := by
  rw [eisensteinClass_difference_three_iff _ _
    (eisensteinTriadUnits s a-eisensteinTriadUnits t b) (by
      funext i
      change eisensteinTriadVector s a i-eisensteinTriadVector t b i =
        3*(eisensteinTriadUnits s a i-eisensteinTriadUnits t b i)
      by_cases hi : i ∈ s <;> by_cases hj : i ∈ t <;>
        simp [eisensteinTriadLatticeVector,eisensteinTriadVector,eisensteinTriadUnits,
          hi,hj,mul_sub])]
  rw [eisensteinTriadUnits_difference_dvd s t hs ht a b]
  have he : eisensteinWordResidue (eisensteinTriadUnits s a-eisensteinTriadUnits t b) =
      ternaryTriadWord s-ternaryTriadWord t := by
    calc
      _ = eisensteinWordResidue (eisensteinTriadUnits s a)-
          eisensteinWordResidue (eisensteinTriadUnits t b) := by ext i; simp [eisensteinWordResidue]
      _ = _ := by rw [eisensteinTriadUnits_residue,eisensteinTriadUnits_residue]
  rw [he]

theorem eisensteinTriadUnits_sum_dvd (s t : Finset (Fin 12))
    (hs : s.card=3) (ht : t.card=3) (a b : TernaryWord) :
    (3 : Eisenstein) ∣ ∑ i,(eisensteinTriadUnits s a+eisensteinTriadUnits t b) i ↔
      (∑ i ∈ s,a i)+(∑ i ∈ t,b i)=0 := by
  simp only [Pi.add_apply,Finset.sum_add_distrib,eisensteinTriadUnits_sum s hs a,
    eisensteinTriadUnits_sum t ht b]
  rw [show (3+eisensteinTheta*(∑ i ∈ s,eisensteinPhaseCorrection (a i))) +
      (3+eisensteinTheta*(∑ i ∈ t,eisensteinPhaseCorrection (b i))) =
      6+eisensteinTheta*((∑ i ∈ s,eisensteinPhaseCorrection (a i))+
        (∑ i ∈ t,eisensteinPhaseCorrection (b i))) by ring]
  rw [dvd_add_right (show (3 : Eisenstein) ∣ 6 from ⟨2,by norm_num⟩),
    eisenstein_three_dvd_theta_iff,← eisensteinResidue_eq_zero]
  simp only [map_add,map_sum,eisensteinPhaseCorrection_residue,Finset.sum_neg_distrib]
  rw [← neg_add,neg_eq_zero]

theorem eisensteinTriadClass_eq_neg_iff (s t : Finset (Fin 12))
    (hs : s.card=3) (ht : t.card=3) (a b : TernaryWord) :
    eisensteinClass (eisensteinTriadLatticeVector s hs a) =
      -eisensteinClass (eisensteinTriadLatticeVector t ht b) ↔
    ternaryTriadWord s+ternaryTriadWord t ∈ ternaryGolay ∧
      (∑ i ∈ s,a i)+(∑ i ∈ t,b i)=0 := by
  rw [← map_neg,eisensteinClass_difference_three_iff _ _
    (eisensteinTriadUnits s a+eisensteinTriadUnits t b) (by
      funext i
      change eisensteinTriadVector s a i-(-eisensteinTriadVector t b i) =
        3*(eisensteinTriadUnits s a i+eisensteinTriadUnits t b i)
      rw [sub_neg_eq_add]
      by_cases hi : i ∈ s <;> by_cases hj : i ∈ t <;>
        simp [eisensteinTriadLatticeVector,eisensteinTriadVector,eisensteinTriadUnits,
          hi,hj,mul_add])]
  rw [eisensteinTriadUnits_sum_dvd s t hs ht a b]
  have he : eisensteinWordResidue (eisensteinTriadUnits s a+eisensteinTriadUnits t b) =
      ternaryTriadWord s+ternaryTriadWord t := by
    calc
      _ = eisensteinWordResidue (eisensteinTriadUnits s a)+
          eisensteinWordResidue (eisensteinTriadUnits t b) := by ext i; simp [eisensteinWordResidue]
      _ = _ := by rw [eisensteinTriadUnits_residue,eisensteinTriadUnits_residue]
  rw [he]

theorem eisensteinTriadFrame_eq_iff (s t : Finset (Fin 12))
    (hs : s.card=3) (ht : t.card=3) (a b : TernaryWord) :
    eisensteinTriadFrame s hs a = eisensteinTriadFrame t ht b ↔
    (ternaryTriadWord s-ternaryTriadWord t ∈ ternaryGolay ∧
      ∑ i ∈ s,a i = ∑ i ∈ t,b i) ∨
    (ternaryTriadWord s+ternaryTriadWord t ∈ ternaryGolay ∧
      (∑ i ∈ s,a i)+(∑ i ∈ t,b i)=0) := by
  rw [Subtype.ext_iff]
  change eisensteinFramePair (eisensteinClass (eisensteinTriadLatticeVector s hs a)) =
    eisensteinFramePair (eisensteinClass (eisensteinTriadLatticeVector t ht b)) ↔ _
  rw [eisensteinFramePair_eq_iff,eisensteinTriadClass_eq_iff,eisensteinTriadClass_eq_neg_iff]

end Atlas.Lattices

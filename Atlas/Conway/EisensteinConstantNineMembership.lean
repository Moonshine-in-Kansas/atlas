import Atlas.Conway.EisensteinConstantNineParameters

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

 theorem eisensteinConstantNinePhaseWord_sum (p : TernaryConstantHexadPair) (r : Bool)
    (b : ZMod 3) (a : TernaryHexadAffinePhase (eisensteinNinePartitionCode p r) b) :
    ∑ i ∈ eisensteinNinePartitionSide p r,eisensteinConstantNinePhaseWord p r b a i=b := by
  have hs : ternarySupport (eisensteinNinePartitionCode p r).val.val=eisensteinNinePartitionSide p r :=
    ternaryConstantHexadCodeword_support _ _
  have he : (∑ i : ternarySupport (eisensteinNinePartitionCode p r).val.val,
      (eisensteinNinePartitionCode p r).val.val i.val*a.val i)=b := a.property
  have hc (i : ternarySupport (eisensteinNinePartitionCode p r).val.val) :
      (eisensteinNinePartitionCode p r).val.val i.val=1 := by
    have hi : i.val ∈ eisensteinNinePartitionSide p r := hs ▸ i.property
    simp [eisensteinNinePartitionCode,ternaryConstantHexadCodeword,ternaryTriadWord,hi]
  simp_rw [hc,one_mul] at he
  rw [← hs,← Finset.sum_coe_sort]
  convert he using 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [eisensteinConstantNinePhaseWord,i.property]

 theorem eisensteinConstantNineParameterVector_mem (p : TernaryConstantHexadPair) (b : ZMod 3)
    (a : EisensteinConstantNineParameters p b) :
    eisensteinConstantNineParameterVector p b a ∈ eisensteinLeechModule := by
  rw [eisensteinConstantNineParameterVector,eisensteinLeechModule_theta_iff]
  let d : Eisenstein := if a.2.1 then -1 else 1
  let S := eisensteinNinePartitionSide p a.1
  let A := eisensteinConstantNinePhaseWord p a.1 b a.2.2.2.1
  have hr : eisensteinWordResidue (eisensteinConstantNineParameterLift p b a)=
      eisensteinResidue d • ternaryTriadWord S := by
    funext i
    change eisensteinResidue (d*((if i ∈ S then eisensteinPhase (A i) else 0)-
      if i=a.2.2.1.val then eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase a.2.2.2.2 else 0))=
      eisensteinResidue d*(if i ∈ S then 1 else 0)
    by_cases hi : i ∈ S <;> by_cases hij : i=a.2.2.1.val <;>
      simp only [hi,hij,ite_true,ite_false,map_mul,map_sub,map_zero,eisensteinPhase_residue,
      show eisensteinResidue eisensteinTheta=0 by decide +kernel,zero_mul,ite_self,sub_zero]
    all_goals split_ifs <;> simp only [eisensteinPhase_residue,map_zero]
  refine ⟨?_,?_⟩
  · rw [hr]
    exact ternaryGolay.smul_mem _ ((mem_ternaryConstantHexads _).mp
      (eisensteinNinePartitionSide_mem p a.1)).2
  · let Z : Eisenstein := (∑ i ∈ S,eisensteinPhaseCorrection (A i))-
        eisensteinPhaseCorrection b*eisensteinPhase a.2.2.2.2
    have hs : ∑ i,eisensteinConstantNineParameterLift p b a i=d*(6+eisensteinTheta*Z) := by
      change (∑ i,d*((if i ∈ S then eisensteinPhase (A i) else 0)-
        if i=a.2.2.1.val then eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase a.2.2.2.2 else 0))=_
      rw [← Finset.mul_sum,Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      simp_rw [eisensteinPhase_correction]
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.sum_mul,← Finset.mul_sum,
        nsmul_eq_mul,mul_one]
      rw [show S.card=6 from ((mem_ternaryConstantHexads _).mp (eisensteinNinePartitionSide_mem p a.1)).1]
      dsimp [Z]
      rw [eisensteinPhase_correction]
      ring
    have hz : eisensteinResidue Z=0 := by
      simp only [Z,map_sub,map_sum,map_mul,eisensteinPhaseCorrection_residue,
        eisensteinPhase_residue,mul_one,Finset.sum_neg_distrib]
      rw [eisensteinConstantNinePhaseWord_sum]
      ring
    have hz3 : (3 : Eisenstein) ∣ eisensteinTheta*Z :=
      (eisenstein_three_dvd_theta_iff Z).mpr ((eisensteinResidue_eq_zero Z).mp hz)
    rw [hs]
    exact (dvd_add (show (3 : Eisenstein) ∣ 6 from ⟨2,by norm_num⟩) hz3).mul_left d

def eisensteinConstantNineParameterLattice (p : TernaryConstantHexadPair) (b : ZMod 3)
    (a : EisensteinConstantNineParameters p b) : EisensteinLattice :=
  ⟨eisensteinConstantNineParameterVector p b a,eisensteinConstantNineParameterVector_mem p b a⟩

end Atlas.Conway

import Atlas.Lattices.EisensteinBalancedNineParameters

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

theorem eisensteinBalancedNinePhaseWord_weighted (c : TernaryBalancedWords) (b : Bool)
    (a : EisensteinBalancedNinePhase c b) :
    ∑ i,c.val.val i*eisensteinBalancedNinePhaseWord c b a i=ternaryBalancedNineSign b := by
  have he : (∑ i ∈ ternarySupport c.val.val,c.val.val i*eisensteinBalancedNinePhaseWord c b a i)=
      ∑ i,c.val.val i*eisensteinBalancedNinePhaseWord c b a i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hn
    have hz : c.val.val i=0 := by simpa [ternarySupport] using hn
    rw [hz,zero_mul]
  rw [← he,← Finset.sum_coe_sort]
  change (∑ i : ternarySupport c.val.val,c.val.val i.val*
    eisensteinBalancedNinePhaseWord c b a i.val)=_
  have ha := a.prop
  change (∑ i : ternarySupport c.val.val,c.val.val i.val*a.val i)=_ at ha
  calc
    _ = ∑ i : ternarySupport c.val.val,c.val.val i.val*a.val i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [eisensteinBalancedNinePhaseWord,dif_pos i.prop]
      congr 1
    _ = _ := ha

theorem eisensteinBalancedNineParameterLift_residue (p : EisensteinBalancedNineParameters) :
    eisensteinWordResidue (eisensteinBalancedNineParameterLift p)=p.1.val.val := by
  have hl : ∀ a : ZMod 3,eisensteinResidue (ternarySignedLift a : Eisenstein)=a := by decide +kernel
  ext i
  by_cases hi : i=p.2.1.val <;>
    simp [eisensteinBalancedNineParameterLift,eisensteinWordResidue,hi,hl,
      show eisensteinResidue eisensteinTheta=0 by decide +kernel]

theorem eisensteinBalancedNineParameterVector_mem (p : EisensteinBalancedNineParameters) :
    eisensteinBalancedNineParameterVector p ∈ eisensteinLeechModule := by
  rw [eisensteinBalancedNineParameterVector,eisensteinLeechModule_theta_iff]
  refine ⟨?_,?_⟩
  · rw [eisensteinBalancedNineParameterLift_residue]
    exact p.1.val.prop
  · let A := eisensteinBalancedNinePhaseWord p.1 p.2.2.1 p.2.2.2.1
    let Z : Eisenstein := (∑ i,(ternarySignedLift (p.1.val.val i) : Eisenstein)*
      eisensteinPhaseCorrection (A i))+eisensteinBalancedNineSign p.2.2.1*eisensteinPhase p.2.2.2.2
    have hs : (∑ i,eisensteinBalancedNineParameterLift p i)=eisensteinTheta*Z := by
      simp only [eisensteinBalancedNineParameterLift,Finset.sum_add_distrib,Finset.sum_ite_eq,
        Finset.mem_univ,ite_true]
      have he (i : Fin 12) :
          (ternarySignedLift (p.1.val.val i) : Eisenstein)*eisensteinPhase (A i)=
            (ternarySignedLift (p.1.val.val i) : Eisenstein)+eisensteinTheta*
              ((ternarySignedLift (p.1.val.val i) : Eisenstein)*eisensteinPhaseCorrection (A i)) := by
        rw [eisensteinPhase_correction]; ring
      change (∑ i,(ternarySignedLift (p.1.val.val i) : Eisenstein)*eisensteinPhase (A i))+_= _
      simp_rw [he]
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Int.cast_sum,
        ternaryBalanced_signed_sum p.1.val.val p.1.prop,Int.cast_zero,zero_add]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      dsimp [Z]
      ring
    rw [hs,eisenstein_three_dvd_theta_iff,← eisensteinResidue_eq_zero]
    have hl : ∀ a : ZMod 3,eisensteinResidue (ternarySignedLift a : Eisenstein)=a := by decide +kernel
    have hb : ∀ b : Bool,eisensteinResidue (eisensteinBalancedNineSign b)=ternaryBalancedNineSign b := by
      decide +kernel
    simp only [Z,map_add,map_sum,map_mul,hl,eisensteinPhaseCorrection_residue,hb,
      eisensteinPhase_residue,mul_one,mul_neg,Finset.sum_neg_distrib]
    rw [eisensteinBalancedNinePhaseWord_weighted]
    exact neg_add_cancel _

def eisensteinBalancedNineParameterLatticeVector (p : EisensteinBalancedNineParameters) :
    EisensteinLattice := ⟨eisensteinBalancedNineParameterVector p,eisensteinBalancedNineParameterVector_mem p⟩

end Atlas.Lattices

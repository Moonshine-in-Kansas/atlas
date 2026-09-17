import Atlas.Lattices.EisensteinBalancedPhases
import Atlas.Lattices.EisensteinThetaClasses

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

def eisensteinBalancedPhasedLift (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) : EisensteinCoordinates :=
  eisensteinDiagonal (eisensteinBalancedPhaseWord c a) (eisensteinBalancedHexadLift c j.val)

theorem eisensteinBalancedPhasedVector_theta (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :
    eisensteinBalancedPhasedVector c j a=eisensteinTheta • eisensteinBalancedPhasedLift c j a := by
  funext i
  simp [eisensteinBalancedPhasedVector,eisensteinBalancedPhasedLift,eisensteinBalancedHexadVector,
    eisensteinDiagonal,mul_comm,mul_left_comm,mul_assoc]

theorem eisensteinBalancedPhasedLift_residue (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :
    eisensteinWordResidue (eisensteinBalancedPhasedLift c j a)=c.val.val := by
  calc
    _ = eisensteinWordResidue (eisensteinBalancedHexadLift c j.val) := by
      ext i
      simp [eisensteinWordResidue,eisensteinBalancedPhasedLift,eisensteinDiagonal]
    _ = _ := eisensteinBalancedHexadLift_residue c j.val

/-- A shared oriented theta class recovers the same balanced residue word.
Nonzero constant shifts would have weight nine rather than six. -/
theorem eisensteinBalancedClass_code (c d : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (k : ternarySupport d.val.val)
    (a : EisensteinBalancedPhase c) (b : EisensteinBalancedPhase d)
    (h : eisensteinClass (eisensteinBalancedPhasedLatticeVector c j a)=
      eisensteinClass (eisensteinBalancedPhasedLatticeVector d k b)) : c=d := by
  have hm := (eisensteinClass_theta_difference_iff _ _ _ _
    (eisensteinBalancedPhasedVector_theta c j a) (eisensteinBalancedPhasedVector_theta d k b)).mp h
  obtain ⟨m,hm⟩ := hm
  have he (i : Fin 12) : c.val.val i-d.val.val i=eisensteinResidue m := by
    have hr := eisensteinCongruence_residue _ m hm i
    have hc := congrFun (eisensteinBalancedPhasedLift_residue c j a) i
    have hd := congrFun (eisensteinBalancedPhasedLift_residue d k b) i
    change eisensteinResidue (eisensteinBalancedPhasedLift c j a i)=c.val.val i at hc
    change eisensteinResidue (eisensteinBalancedPhasedLift d k b i)=d.val.val i at hd
    simpa only [eisensteinWordResidue,Pi.sub_apply,map_sub,hc,hd] using hr
  have hword : (fun i => d.val.val i+eisensteinResidue m)=c.val.val := by
    funext i
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp (he i)).symm
  have hz := ternaryBalanced_constant_shift d.val.val d.prop (eisensteinResidue m)
    (hword.symm ▸ c.prop)
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have hi := he i
  rw [hz,sub_eq_zero] at hi
  exact hi

end Atlas.Lattices

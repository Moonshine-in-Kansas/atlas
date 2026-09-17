import Atlas.Lattices.EisensteinBalancedClassCode
import Atlas.Codes.TernaryHexadLines

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

def eisensteinBalancedDifferenceLift (c : TernaryBalancedWords)
    (j k : ternarySupport c.val.val) (a b : EisensteinBalancedPhase c) : EisensteinCoordinates := fun i =>
  (ternarySignedLift (c.val.val i) : Eisenstein)*
      (eisensteinPhaseCorrection (eisensteinBalancedPhaseWord c a i)-
        eisensteinPhaseCorrection (eisensteinBalancedPhaseWord c b i)) +
    eisensteinTheta*((ternarySignedLift (c.val.val i) : Eisenstein)*
      ((if i=j.val then eisensteinPhase (eisensteinBalancedPhaseWord c a i) else 0)-
       (if i=k.val then eisensteinPhase (eisensteinBalancedPhaseWord c b i) else 0)))

theorem eisensteinBalancedDifferenceLift_theta (c : TernaryBalancedWords)
    (j k : ternarySupport c.val.val) (a b : EisensteinBalancedPhase c) :
    eisensteinBalancedPhasedLift c j a-eisensteinBalancedPhasedLift c k b =
      eisensteinTheta • eisensteinBalancedDifferenceLift c j k a b := by
  have h3 : eisensteinTheta^3 = -3*eisensteinTheta := by
    calc
      eisensteinTheta^3=eisensteinTheta^2*eisensteinTheta := by ring
      _ = _ := by rw [eisensteinTheta_sq]
  funext i
  have hc (l : ternarySupport c.val.val) :
      (if i=l.val then 3*(ternarySignedLift (c.val.val l.val) : Eisenstein) else 0) =
        (if i=l.val then 3 else 0)*(ternarySignedLift (c.val.val i) : Eisenstein) := by
    by_cases h : i=l.val <;> simp [h]
  simp only [eisensteinBalancedPhasedLift,eisensteinDiagonal,eisensteinBalancedHexadLift,
    eisensteinBalancedDifferenceLift,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hc]
  by_cases hj : i=j.val <;> by_cases hk : i=k.val <;>
    simp_all only [ite_true,ite_false]
  all_goals simp_rw [eisensteinPhase_correction]
  all_goals ring_nf
  all_goals simp only [eisensteinTheta_sq,h3]
  all_goals ring

theorem eisensteinBalancedDifferenceLift_residue (c : TernaryBalancedWords)
    (j k : ternarySupport c.val.val) (a b : EisensteinBalancedPhase c) :
    eisensteinWordResidue (eisensteinBalancedDifferenceLift c j k a b) =
      fun i => c.val.val i*(-eisensteinBalancedPhaseWord c a i+eisensteinBalancedPhaseWord c b i) := by
  have hs : ∀ x : ZMod 3,eisensteinResidue (ternarySignedLift x : Eisenstein)=x := by decide +kernel
  ext i
  simp [eisensteinWordResidue,eisensteinBalancedDifferenceLift,hs,
    show eisensteinResidue eisensteinTheta=0 by decide +kernel]

/-- The code support line forces all relative phases in a shared oriented class
to be one global scalar phase. -/
theorem eisensteinBalancedClass_phases (c : TernaryBalancedWords)
    (j k : ternarySupport c.val.val) (a b : EisensteinBalancedPhase c)
    (h : eisensteinClass (eisensteinBalancedPhasedLatticeVector c j a)=
      eisensteinClass (eisensteinBalancedPhasedLatticeVector c k b)) :
    ∃ r : ZMod 3,∀ i : ternarySupport c.val.val,b.val i=a.val i+r := by
  have hm := (eisensteinClass_theta_difference_iff _ _ _ _
    (eisensteinBalancedPhasedVector_theta c j a) (eisensteinBalancedPhasedVector_theta c k b)).mp h
  rw [eisensteinBalancedDifferenceLift_theta] at hm
  let w : ternaryGolay := ⟨eisensteinWordResidue (eisensteinBalancedDifferenceLift c j k a b),
    eisensteinLeechModule_theta_code _ hm⟩
  have hs : ternarySupport w.val ⊆ ternarySupport c.val.val := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hz
    apply hn
    change eisensteinWordResidue (eisensteinBalancedDifferenceLift c j k a b) i=0
    rw [eisensteinBalancedDifferenceLift_residue]
    change c.val.val i*_=0
    rw [hz,zero_mul]
  obtain ⟨r,hr⟩ := ternaryGolay_supported_hexad (ternaryBalancedSixWord c) w hs
  refine ⟨r,?_⟩
  intro i
  have hi := congrFun hr i.val
  change eisensteinWordResidue (eisensteinBalancedDifferenceLift c j k a b) i.val =
    r*c.val.val i.val at hi
  rw [eisensteinBalancedDifferenceLift_residue] at hi
  simp only [eisensteinBalancedPhaseWord,dif_pos i.prop] at hi
  change c.val.val i.val*(-a.val i+b.val i)=r*c.val.val i.val at hi
  have hn := (Finset.mem_filter.mp i.prop).2
  have hd : b.val i-a.val i=r := by
    apply mul_left_cancel₀ hn
    simpa only [sub_eq_add_neg,add_comm,mul_comm] using hi
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hd

end Atlas.Lattices

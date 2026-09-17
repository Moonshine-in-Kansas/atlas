import Atlas.Lattices.EisensteinCongruenceCriteria
import Atlas.Lattices.EisensteinShortClasses

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

/-- An exact theta-class criterion for differences divisible coordinatewise by
three. It keeps both the code and the sum congruence. -/
theorem eisensteinClass_difference_three_iff (x y : EisensteinLattice)
    (v : EisensteinCoordinates) (hv : x.val-y.val = (3 : Eisenstein) • v) :
    eisensteinClass x = eisensteinClass y ↔
      eisensteinWordResidue v ∈ ternaryGolay ∧ (3 : Eisenstein) ∣ ∑ i,v i := by
  have he : eisensteinClass x = eisensteinClass y ↔
      eisensteinTheta • (-v) ∈ eisensteinLeechModule := by
    constructor
    · intro h
      obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
      have hwv : w.val = eisensteinTheta • (-v) := by
        funext i
        apply eisenstein_theta_cancel
        have hi := congrArg (fun z : EisensteinLattice => z.val i) hw
        have hiv := congrFun hv i
        change x.val i-y.val i = 3*v i at hiv
        change eisensteinTheta*w.val i=x.val i-y.val i at hi
        rw [hi,hiv]
        simp [Pi.smul_apply,smul_eq_mul,← mul_assoc,← pow_two,eisensteinTheta_sq]
      exact hwv ▸ w.property
    · intro h
      apply (Submodule.Quotient.eq _).mpr
      refine ⟨⟨eisensteinTheta • (-v),h⟩,?_⟩
      apply Subtype.ext
      change eisensteinTheta • (eisensteinTheta • (-v)) = x.val-y.val
      rw [hv]
      funext i
      simp [eisensteinThetaEnd,Pi.smul_apply,smul_eq_mul,← mul_assoc,
        ← pow_two,eisensteinTheta_sq]
  rw [he,eisensteinLeechModule_theta_iff]
  have hn : eisensteinWordResidue (-v) = -eisensteinWordResidue v := by
    ext i; simp [eisensteinWordResidue]
  rw [hn]
  simp only [Submodule.neg_mem_iff,Pi.neg_apply,Finset.sum_neg_distrib,dvd_neg]

end Atlas.Lattices

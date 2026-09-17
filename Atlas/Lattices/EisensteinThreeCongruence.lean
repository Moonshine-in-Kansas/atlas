import Atlas.Lattices.EisensteinCongruenceCriteria

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

theorem eisensteinLeechModule_three_iff (u : EisensteinCoordinates) :
    (3 : Eisenstein) • u ∈ eisensteinLeechModule ↔ eisensteinTheta ∣ ∑ i,u i := by
  have he : (3 : Eisenstein) • u=eisensteinTheta • (-eisensteinTheta • u) := by
    funext i
    simp [Pi.smul_apply,smul_eq_mul,← mul_assoc,← pow_two,eisensteinTheta_sq]
  rw [he,eisensteinLeechModule_theta_iff]
  have hz : eisensteinWordResidue (-eisensteinTheta • u)=0 := by
    ext i
    simp [eisensteinWordResidue,show eisensteinResidue eisensteinTheta=0 by decide +kernel]
  rw [hz]
  simp only [Submodule.zero_mem,true_and,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,
    neg_mul,Finset.sum_neg_distrib,dvd_neg,eisenstein_three_dvd_theta_iff]

end Atlas.Lattices

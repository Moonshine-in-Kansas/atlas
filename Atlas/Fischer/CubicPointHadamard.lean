import Atlas.Fischer.CubicPointRows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1500000 in
/-- Three actual point-slice rows, contracted at one common coordinate. -/
theorem cubicPointPattern_row_pair (p q r : Omega) :
    (∑ i : Omega,cubicPointPattern p r i*cubicPointPattern q r i)=
      216+256*(if p=q then (1 : Scalar) else 0)-
      1536*((if p=r then 1 else 0)+(if q=r then 1 else 0))+
      14336*(if p=q then if q=r then 1 else 0 else 0) := by
  have hc : Fintype.card Omega=24 := by decide
  simp only [cubicPointPattern_normalForm,mul_add,add_mul,mul_sub,sub_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul]
  by_cases hpq : p=q
  · subst q
    by_cases hpr : p=r
    · subst r
      simp [Finset.sum_ite_irrel,hc]
      norm_num
    · simp [hpr,Ne.symm hpr,Finset.sum_ite_irrel,hc]
      norm_num
  · by_cases hpr : p=r
    · subst r
      simp [hpq,Ne.symm hpq,Finset.sum_ite_irrel,hc]
      norm_num
    · by_cases hqr : q=r
      · subst r
        simp [hpq,Ne.symm hpq,Finset.sum_ite_irrel,hc]
        norm_num
      · simp [hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr,Finset.sum_ite_irrel,hc]
        norm_num

set_option maxHeartbeats 3000000 in
/-- The Hadamard contraction of three point slices, derived symbolically
from Kronecker sums, rather than by coordinate enumeration. -/
theorem cubicPointPattern_hadamard_triple (p q r : Omega) :
    (∑ a : Omega,∑ i : Omega,cubicPointPattern p a i*cubicPointPattern q a i*
      cubicPointPattern r a i)=
      16320+135168*((if p=q then (1 : Scalar) else 0)+
        (if p=r then 1 else 0)+(if q=r then 1 else 0))-
      720896*(if p=q then if q=r then 1 else 0 else 0) := by
  have hc : Fintype.card Omega=24 := by decide
  simp only [cubicPointPattern_normalForm,mul_add,add_mul,mul_sub,sub_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul]
  by_cases hpq : p=q
  · subst q
    by_cases hpr : p=r
    · subst r
      simp [Finset.sum_ite_irrel,hc]
      norm_num
    · simp [hpr,Ne.symm hpr,Finset.sum_ite_irrel,hc]
      norm_num
  · by_cases hpr : p=r
    · subst r
      simp [hpq,Ne.symm hpq,Finset.sum_ite_irrel,hc]
      norm_num
    · by_cases hqr : q=r
      · subst r
        simp [hpq,Ne.symm hpq,Finset.sum_ite_irrel,hc]
        norm_num
      · simp [hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr,Finset.sum_ite_irrel,hc]
        norm_num

end Atlas.Fischer

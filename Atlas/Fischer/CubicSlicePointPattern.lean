import Atlas.Fischer.CubicSliceCoefficients

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Five elementary diagonal/rank-one pieces of the actual point tensor. -/
theorem cubicPointPattern_normalForm (i a b : Omega) :
    cubicPointPattern i a b = (-1 : Scalar)+16*(if a=b then 1 else 0)+
      16*(if a=i then 1 else 0)+16*(if b=i then 1 else 0)-
      128*(if a=i then 1 else 0)*(if b=i then 1 else 0) := by
  unfold cubicPointPattern
  by_cases hab : a=b <;> by_cases hai : a=i <;> by_cases hbi : b=i <;>
    simp_all <;> norm_num <;> aesop

set_option maxHeartbeats 1000000 in
/-- Uniform point-slice contraction, reduced by Kronecker sums rather than
by enumerating pairs of the 783 algebra coordinates. -/
theorem cubicPointPattern_pair_sum (i j : Omega) :
    (∑ a : Omega,∑ b : Omega,cubicPointPattern i a b*cubicPointPattern j a b)=
      if i=j then (22592 : Scalar) else 2112 := by
  have hc : Fintype.card Omega=24 := by decide
  simp only [cubicPointPattern_normalForm,mul_add,add_mul,mul_sub,sub_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul]
  by_cases h : i=j
  · subst j
    simp [Finset.sum_ite_irrel,hc]
    norm_num
  · simp [h,Ne.symm h,Finset.sum_ite_irrel,hc]
    norm_num

end Atlas.Fischer

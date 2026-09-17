import Atlas.Fischer.CubicPointRows

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The point cubic evaluated on three arbitrary vectors: only sums and
coordinatewise products occur. This is the structural reduction used in the
six-index contraction. -/
theorem cubicPointPattern_vector_contraction (x y z : Omega → Scalar) :
    (∑ a,∑ b,∑ c,cubicPointPattern a b c*x a*y b*z c)=
      -(∑ a,x a)*(∑ b,y b)*(∑ c,z c)+
      16*((∑ a,x a*y a)*(∑ c,z c)+(∑ a,x a*z a)*(∑ b,y b)+
        (∑ a,y a*z a)*(∑ b,x b))-128*(∑ a,x a*y a*z a) := by
  have he (a b c : Omega) : cubicPointPattern a b c*x a*y b*z c=
      -x a*y b*z c+
      16*(if b=c then x a*y b*z c else 0)+
      16*(if b=a then x a*y b*z c else 0)+
      16*(if c=a then x a*y b*z c else 0)-
      128*(if b=a then if c=a then x a*y b*z c else 0 else 0) := by
    rw [cubicPointPattern_normalForm]
    by_cases hbc : b=c <;> by_cases hba : b=a <;> by_cases hca : c=a <;>
      simp_all <;> ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  have hm : (∑ a,(∑ b,x a*y b)*z a)=(∑ a,x a*z a)*(∑ b,y b) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
    ring
  rw [hm]
  simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
  simp only [Finset.sum_neg_distrib]
  ring

end Atlas.Fischer

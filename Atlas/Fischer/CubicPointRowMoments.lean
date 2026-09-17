import Atlas.Fischer.CubicPointHadamard
import Atlas.Fischer.CubicPointNetworkReduction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cubicPointDeltaSum (p q r : Omega) : Scalar :=
  (if p=q then 1 else 0)+(if p=r then 1 else 0)+(if q=r then 1 else 0)

def cubicPointDeltaAll (p q r : Omega) : Scalar :=
  if p=q then if q=r then 1 else 0 else 0

theorem cubicPointRowSum_triple_sum (p q r : Omega) :
    (∑ a,cubicPointRowSum p a*cubicPointRowSum q a*cubicPointRowSum r a)=
      61440+524288*cubicPointDeltaSum p q r+16777216*cubicPointDeltaAll p q r := by
  have hc : Fintype.card Omega=24 := by decide
  simp only [cubicPointRowSum,mul_add,add_mul,Finset.sum_add_distrib,
    mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul]
  by_cases hpq : p=q
  · subst q
    by_cases hpr : p=r
    · subst r
      simp [cubicPointDeltaSum,cubicPointDeltaAll,Finset.sum_ite_irrel,hc]
      norm_num
    · simp [cubicPointDeltaSum,cubicPointDeltaAll,hpr,Ne.symm hpr,Finset.sum_ite_irrel,hc]
      norm_num
  · by_cases hpr : p=r
    · subst r
      simp [cubicPointDeltaSum,cubicPointDeltaAll,hpq,Ne.symm hpq,Finset.sum_ite_irrel,hc]
      norm_num
    · by_cases hqr : q=r
      · subst r
        simp [cubicPointDeltaSum,cubicPointDeltaAll,hpq,Ne.symm hpq,Finset.sum_ite_irrel,hc]
        norm_num
      · simp [cubicPointDeltaSum,cubicPointDeltaAll,hpq,hpr,hqr,Ne.symm hpq,
          Ne.symm hpr,Ne.symm hqr,Finset.sum_ite_irrel,hc]
        norm_num

theorem cubicPointPattern_row_weighted (p q r : Omega) :
    (∑ a,cubicPointPattern p a r*cubicPointRowSum q a)=
      8*cubicPointRowSum p r+256*cubicPointPattern p q r := by
  unfold cubicPointRowSum
  simp only [mul_add,mul_ite,mul_zero,mul_one,Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [cubicPointPattern_row_sum]
  unfold cubicPointRowSum
  by_cases h : r=p <;> simp [h] <;> ring

theorem cubicPointPattern_hadamard_weighted (p q r : Omega) :
    (∑ a,∑ i,cubicPointPattern p a i*cubicPointPattern q a i*cubicPointRowSum r a)=
      8*(∑ a,∑ i,cubicPointPattern p a i*cubicPointPattern q a i)+
      256*(∑ i,cubicPointPattern p r i*cubicPointPattern q r i) := by
  unfold cubicPointRowSum
  simp only [mul_add,mul_ite,mul_zero,mul_one,Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  rw [← Finset.sum_mul]
  ring

theorem cubicPointPattern_vector_rows (p q r : Omega) :
    cubicPointVector (cubicPointRowSum p) (cubicPointRowSum q) (cubicPointRowSum r)=
      -448^3+16*448*((∑ a,cubicPointRowSum p a*cubicPointRowSum q a)+
        (∑ a,cubicPointRowSum p a*cubicPointRowSum r a)+
        (∑ a,cubicPointRowSum q a*cubicPointRowSum r a))-
      128*(∑ a,cubicPointRowSum p a*cubicPointRowSum q a*cubicPointRowSum r a) := by
  rw [cubicPointVector,cubicPointPattern_vector_contraction]
  simp_rw [cubicPointRowSum_sum]
  ring

end Atlas.Fischer

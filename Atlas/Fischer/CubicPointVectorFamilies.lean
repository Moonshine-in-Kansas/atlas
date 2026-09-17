import Atlas.Fischer.CubicPointRowMoments

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicPointRowSum_weighted (f : Omega → Scalar) (r : Omega) :
    (∑ i,f i*cubicPointRowSum r i)=8*(∑ i,f i)+256*f r := by
  unfold cubicPointRowSum
  simp only [mul_add,mul_ite,mul_zero,mul_one,Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

theorem cubicPointVector_swap_first (x y z : Omega → Scalar) :
    cubicPointVector x y z=cubicPointVector y x z := by
  unfold cubicPointVector
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [cubicPointPattern_swap_first]
  ring

theorem cubicPointVector_swap_last (x y z : Omega → Scalar) :
    cubicPointVector x y z=cubicPointVector x z y := by
  unfold cubicPointVector
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [cubicPointPattern_swap_last]
  ring

theorem cubicPointVector_two_rows (p q r a : Omega) :
    cubicPointVector (cubicPointPattern p a) (cubicPointPattern q a) (cubicPointRowSum r)=
      -192*cubicPointRowSum p a*cubicPointRowSum q a+
      6144*(∑ i,cubicPointPattern p a i*cubicPointPattern q a i)+
      4096*(cubicPointPattern p a r*cubicPointRowSum q a+
        cubicPointPattern q a r*cubicPointRowSum p a)-
      32768*cubicPointPattern p a r*cubicPointPattern q a r := by
  rw [cubicPointVector,cubicPointPattern_vector_contraction]
  rw [cubicPointPattern_column_sum,cubicPointPattern_column_sum,cubicPointRowSum_sum]
  rw [cubicPointRowSum_weighted,cubicPointRowSum_weighted,cubicPointRowSum_weighted]
  rw [cubicPointPattern_column_sum,cubicPointPattern_column_sum]
  ring

theorem cubicPointVector_two_rows_sum (p q r : Omega) :
    (∑ a,cubicPointVector (cubicPointPattern p a) (cubicPointPattern q a) (cubicPointRowSum r))=
      -192*(∑ a,cubicPointRowSum p a*cubicPointRowSum q a)+
      6144*(∑ a,∑ i,cubicPointPattern p a i*cubicPointPattern q a i)+
      4096*(8*cubicPointRowSum p r+256*cubicPointPattern p q r+
        (8*cubicPointRowSum q r+256*cubicPointPattern q p r))-
      32768*(∑ i,cubicPointPattern p r i*cubicPointPattern q r i) := by
  simp only [cubicPointVector_two_rows,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have he (a : Omega) : -192*cubicPointRowSum p a*cubicPointRowSum q a=
      -192*(cubicPointRowSum p a*cubicPointRowSum q a) := by ring
  have hl (a : Omega) : 32768*cubicPointPattern p a r*cubicPointPattern q a r=
      32768*(cubicPointPattern p r a*cubicPointPattern q r a) := by
    rw [cubicPointPattern_swap_last p a r,cubicPointPattern_swap_last q a r]
    ring
  simp_rw [he,hl,← Finset.mul_sum,Finset.sum_add_distrib]
  rw [cubicPointPattern_row_weighted,cubicPointPattern_row_weighted]

theorem cubicPointVector_three_rows_sum (p q r : Omega) :
    (∑ a,cubicPointVector (cubicPointPattern p a) (cubicPointPattern q a) (cubicPointPattern r a))=
      -(∑ a,cubicPointRowSum p a*cubicPointRowSum q a*cubicPointRowSum r a)+
      16*((∑ a,∑ i,cubicPointPattern p a i*cubicPointPattern q a i*cubicPointRowSum r a)+
        (∑ a,∑ i,cubicPointPattern p a i*cubicPointPattern r a i*cubicPointRowSum q a)+
        (∑ a,∑ i,cubicPointPattern q a i*cubicPointPattern r a i*cubicPointRowSum p a))-
      128*(∑ a,∑ i,cubicPointPattern p a i*cubicPointPattern q a i*cubicPointPattern r a i) := by
  have he (a : Omega) := cubicPointPattern_vector_contraction
    (cubicPointPattern p a) (cubicPointPattern q a) (cubicPointPattern r a)
  simp only [cubicPointPattern_column_sum] at he
  simp only [cubicPointVector,he,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  simp only [neg_mul,Finset.sum_neg_distrib,Finset.sum_add_distrib] <;> ring

end Atlas.Fischer

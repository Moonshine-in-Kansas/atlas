import Atlas.Fischer.CubicSlicePointPattern

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicPointPattern_swap_first (p i j : Omega) :
    cubicPointPattern p i j=cubicPointPattern i p j := by
  have h := coordinateCubic_swap_first (.inl p) (.inl i) (.inl j)
  rw [coordinateCubic_points,coordinateCubic_points] at h
  linear_combination 1024*h

theorem cubicPointPattern_swap_last (p i j : Omega) :
    cubicPointPattern p i j=cubicPointPattern p j i := by
  have h := coordinateCubic_swap_last (.inl p) (.inl i) (.inl j)
  rw [coordinateCubic_points,coordinateCubic_points] at h
  linear_combination 1024*h

/-- Actual row sum
 of a pure-point cubic slice. -/
def cubicPointRowSum (p i : Omega) : Scalar := 8+256*(if i=p then 1 else 0)

theorem cubicPointPattern_row_sum (p i : Omega) :
    (∑ a : Omega,cubicPointPattern p a i)=cubicPointRowSum p i := by
  have hc : Fintype.card Omega=24 := by decide
  simp only [cubicPointPattern_normalForm,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul]
  by_cases hi : i=p
  · subst i
    simp [cubicPointRowSum,Finset.sum_ite_irrel,hc]
    norm_num
  · simp [cubicPointRowSum,hi,Ne.symm hi,Finset.sum_ite_irrel,hc]
    norm_num

theorem cubicPointPattern_column_sum (p a : Omega) :
    (∑ i : Omega,cubicPointPattern p a i)=cubicPointRowSum p a := by
  simp_rw [cubicPointPattern_swap_last p a]
  exact cubicPointPattern_row_sum p a

theorem cubicPointRowSum_sum
 (p : Omega) : (∑ i : Omega,cubicPointRowSum p i)=448 := by
  have hc : Fintype.card Omega=24 := by decide
  simp [cubicPointRowSum,Finset.sum_add_distrib,Finset.sum_ite_irrel,hc]
  norm_num

theorem cubicPointPattern_total_sum (p : Omega) :
    (∑ i : Omega,∑ a : Omega,cubicPointPattern p a i)=448 := by
  simp_rw [cubicPointPattern_row_sum]
  exact cubicPointRowSum_sum p

theorem cubicPointRowSum_pair_sum (p q : Omega) :
    (∑ i : Omega,cubicPointRowSum p i*cubicPointRowSum q i)=
      5632+65536*(if p=q then (1 : Scalar) else 0) := by
  have hc : Fintype.card Omega=24 := by decide
  simp only [cubicPointRowSum,mul_add,add_mul,Finset.sum_add_distrib,
    mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul]
  by_cases h : p=q
  · subst q
    simp [Finset.sum_ite_irrel,hc]
    norm_num
  · simp [h,Ne.symm h,Finset.sum_ite_irrel,hc]
    norm_num

end Atlas.Fischer

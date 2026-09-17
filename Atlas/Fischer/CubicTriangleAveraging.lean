import Atlas.Fischer.CubicTriangleIncidence

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The numerator for a specified equality pattern with exactly two equal
positions. This is a finite-sum identity, before any transitivity averaging. -/
theorem cubicTriangle_two_equal_sum {I R : Type*} [Fintype I] [CommRing R]
    (a b c : I → R) :
    (∑ i,∑ j,if i ≠ j then a i*b i*c j else 0)=
      (∑ i,a i*b i)*(∑ j,c j)-(∑ i,a i*b i*c i) := by
  have h (i j : I) : (if i ≠ j then a i*b i*c j else 0)=
      a i*b i*c j-(if i=j then a i*b i*c j else 0) := by
    by_cases hij : i=j <;> simp [hij]
  simp_rw [h,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Finset.sum_mul_sum]

/-- The three equality patterns are separated by inclusion-exclusion on the
coordinate positions, without assuming a permutation action. -/
theorem cubicTriangle_distinct_sum {I R : Type*} [Fintype I] [CommRing R]
    (a b c : I → R) :
    (∑ i,∑ j,∑ k,if i ≠ j ∧ i ≠ k ∧ j ≠ k then a i*b j*c k else 0)=
      (∑ i,a i)*(∑ j,b j)*(∑ k,c k)-
      (∑ i,a i*b i)*(∑ k,c k)-
      (∑ i,a i*c i)*(∑ j,b j)-
      (∑ j,b j*c j)*(∑ i,a i)+2*(∑ i,a i*b i*c i) := by
  have h (i j k : I) :
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k then a i*b j*c k else 0)=
      a i*b j*c k-(if i=j then a i*b j*c k else 0)-
      (if i=k then a i*b j*c k else 0)-
      (if j=k then a i*b j*c k else 0)+
      2*(if i=j ∧ j=k then a i*b j*c k else 0) := by
    by_cases hij : i=j <;> by_cases hik : i=k <;> by_cases hjk : j=k <;>
      simp_all <;> ring
  simp_rw [h,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  have hd : (∑ i,∑ j,∑ k,if i=j then if j=k then a i*b j*c k else 0 else 0)=
      ∑ i,a i*b i*c i := by
    simp [Finset.sum_ite_irrel]
  have hm :
 (∑ i,(∑ j,a i*b j)*c i)=(∑ i,a i*c i)*(∑ j,b j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum]
    ring
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  rw [hd,hm]
  simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
  ring


end Atlas.Fischer

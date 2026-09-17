import Atlas.Fischer.RootRigidity

namespace Atlas.Fischer
attribute [local instance] Classical.propDecidable

@[simp] theorem hermitian_zero_left (x : Coordinates) : hermitian 0 x = 0 := by
  simp [hermitian, weightedHermitian]

@[simp] theorem hermitian_zero_right (x : Coordinates) : hermitian x 0 = 0 := by
  simp [hermitian, weightedHermitian]

theorem hermitian_sum_left {ι : Type*} (s : Finset ι) (f : ι → Coordinates) (y : Coordinates) :
    hermitian (∑ i ∈ s, f i) y = ∑ i ∈ s, hermitian (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, hermitian_add_left, ih]

theorem hermitian_sum_right {ι : Type*} (s : Finset ι) (x : Coordinates) (f : ι → Coordinates) :
    hermitian x (∑ i ∈ s, f i) = ∑ i ∈ s, hermitian x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, hermitian_add_right, ih]

theorem hermitian_orthonormal_sum {ι : Type*} [Fintype ι]
    (v : ι → Coordinates) (hv : ∀ i j, hermitian (v i) (v j) = if i = j then 1 else 0)
    (c : ι → Scalar) :
    hermitian (∑ i, c i • v i) (∑ i, c i • v i) = ∑ i, c i * star (c i) := by
  classical
  simp only [hermitian_sum_left, hermitian_sum_right, hermitian_smul_left,
    hermitian_smul_right, hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_comm]

end Atlas.Fischer

import Atlas.Fischer.CubicPointVectorContraction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cubicPointVector (x y z : Omega → Scalar) : Scalar :=
  ∑ i,∑ j,∑ k,cubicPointPattern i j k*x i*y j*z k

def cubicPointMatrixRowSum (x : Omega → Omega → Scalar) (i : Omega) : Scalar := ∑ a,x a i

def cubicPointNetwork (x y z : Omega → Omega → Scalar) : Scalar :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,
    cubicPointPattern i j k*cubicPointPattern a b c*x a i*y b j*z c k

/-- Fubini for the common row label in three point vectors. -/
theorem cubicPointVector_diagonal_sum (x y z : Omega → Omega → Scalar) :
    (∑ i,∑ j,∑ k,cubicPointPattern i j k*(∑ a,x a i*y a j*z a k))=
      ∑ a,cubicPointVector (x a) (y a) (z a) := by
  simp_rw [Finset.mul_sum]
  calc
    _=∑ i,∑ j,∑ a,∑ k,cubicPointPattern i j k*(x a i*y a j*z a k) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _=∑ i,∑ a,∑ j,∑ k,cubicPointPattern i j k*(x a i*y a j*z a k) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _=∑ a,∑ i,∑ j,∑ k,cubicPointPattern i j k*(x a i*y a j*z a k) := Finset.sum_comm
    _=_ := by
      unfold cubicPointVector
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem cubicPointNetwork_inner (x y z : Omega → Omega → Scalar) :
    cubicPointNetwork x y z=
      ∑ i,∑ j,∑ k,cubicPointPattern i j k*
        cubicPointVector (fun a => x a i) (fun b => y b j) (fun c => z c k) := by
  unfold cubicPointNetwork cubicPointVector
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-- One outer tensor is eliminated structurally. Applying the vector formula
again leaves at most two contracted coordinates. -/
theorem cubicPointNetwork_reduction (x y z : Omega → Omega → Scalar) :
    cubicPointNetwork x y z=
      -cubicPointVector (cubicPointMatrixRowSum x) (cubicPointMatrixRowSum y) (cubicPointMatrixRowSum z)+
      16*(∑ a,cubicPointVector (x a) (y a) (cubicPointMatrixRowSum z))+
      16*(∑ a,cubicPointVector (x a) (cubicPointMatrixRowSum y) (z a))+
      16*(∑ a,cubicPointVector (cubicPointMatrixRowSum x) (y a) (z a))-
      128*(∑ a,cubicPointVector (x a) (y a) (z a)) := by
  rw [cubicPointNetwork_inner]
  have he (i j k : Omega) :
      cubicPointVector (fun a => x a i) (fun b => y b j) (fun c => z c k)=
      -cubicPointMatrixRowSum x i*cubicPointMatrixRowSum y j*cubicPointMatrixRowSum z k+
      16*(∑ a,x a i*y a j*cubicPointMatrixRowSum z k)+
      16*(∑ a,x a i*cubicPointMatrixRowSum y j*z a k)+
      16*(∑ a,cubicPointMatrixRowSum x i*y a j*z a k)-
      128*(∑ a,x a i*y a j*z a k) := by
    rw [cubicPointVector,cubicPointPattern_vector_contraction]
    unfold cubicPointMatrixRowSum
    have hmid : (∑ a,x a i*(∑ b,y b j)*z a k)=(∑ b,y b j)*(∑ a,x a i*z a k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    rw [hmid]

    simp only [← Finset.sum_mul,← Finset.mul_sum]
    simp only [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
    ring
  simp_rw [he]
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hmul (i j k : Omega) (v : Scalar) (n : Scalar) :
      cubicPointPattern i j k*(n*v)=n*(cubicPointPattern i j k*v) := by ring
  simp_rw [hmul,← Finset.mul_sum]
  rw [cubicPointVector_diagonal_sum,cubicPointVector_diagonal_sum,
    cubicPointVector_diagonal_sum,cubicPointVector_diagonal_sum]
  have hn : (∑ i,∑ j,-cubicPointMatrixRowSum x i*cubicPointMatrixRowSum y j*
      (∑ k,cubicPointPattern i j k*cubicPointMatrixRowSum z k))=
      -cubicPointVector (cubicPointMatrixRowSum x) (cubicPointMatrixRowSum y) (cubicPointMatrixRowSum z) := by
    unfold cubicPointVector
    simp_rw [Finset.mul_sum]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hn]

end Atlas.Fischer

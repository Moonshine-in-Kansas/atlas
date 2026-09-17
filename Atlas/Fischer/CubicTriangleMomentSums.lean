import Atlas.Fischer.CubicTriangleSymmetry

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicTriangle_sum_comm_two {I J T R : Type*} [Fintype I] [Fintype J]
    [Fintype T] [AddCommMonoid R] (f : I → J → T → R) :
    (∑ i,∑ j,∑ t,f i j t)=∑ t,∑ i,∑ j,f i j t := by
  calc
    _=∑ i,∑ t,∑ j,f i j t := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _=_ := Finset.sum_comm

theorem cubicTriangle_sum_comm_three {I J K T R : Type*} [Fintype I] [Fintype J]
    [Fintype K] [Fintype T] [AddCommMonoid R] (f : I → J → K → T → R) :
    (∑ i,∑ j,∑ k,∑ t,f i j k t)=∑ t,∑ i,∑ j,∑ k,f i j k t := by
  calc
    _=∑ i,∑ t,∑ j,∑ k,f i j k t := by
      apply Finset.sum_congr rfl
      intro i hi
      exact cubicTriangle_sum_comm_two (f i)
    _=_ := Finset.sum_comm

theorem cubicTriangle_family_diagonal {T : Type*} [Fintype T]
    (a b c : T → Omega → Scalar) (q : Scalar)
    (hq : ∀ t,(∑ i,a t i*b t i*c t i)=q) :
    (∑ i,∑ t,a t i*b t i*c t i)=(Fintype.card T : Scalar)*q := by
  rw [Finset.sum_comm]
  simp_rw [hq]
  simp

theorem cubicTriangle_family_two_equal {T : Type*} [Fintype T]
    (a b c : T → Omega → Scalar) (p q : Scalar)
    (hc : ∀ t,(∑ i,c t i)=8) (hp : ∀ t,(∑ i,a t i*b t i)=p)
    (hq : ∀ t,(∑ i,a t i*b t i*c t i)=q) :
    (∑ i,∑ j,if i ≠ j then ∑ t,a t i*b t i*c t j else 0)=
      (Fintype.card T : Scalar)*(8*p-q) := by
  have he (i j : Omega) : (if i ≠ j then ∑ t,a t i*b t i*c t j else 0)=
      ∑ t,if i ≠ j then a t i*b t i*c t j else 0 := by
    by_cases h : i=j <;> simp [h]
  simp_rw [he]
  rw [cubicTriangle_sum_comm_two]
  have ht (t : T) : (∑ i,∑ j,if i ≠ j then a t i*b t i*c t j else 0)=p*8-q := by
    have hh := cubicTriangle_two_equal_sum (a t) (b t) (c t)
    simp only [hc,hp,hq] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> rfl

  simp_rw [ht]

  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem cubicTriangle_family_distinct {T : Type*} [Fintype T]
    (a b c : T → Omega → Scalar) (p q : Scalar)
    (ha : ∀ t,(∑ i,a t i)=8) (hb : ∀ t,(∑ i,b t i)=8) (hc : ∀ t,(∑ i,c t i)=8)
    (hab : ∀ t,(∑ i,a t i*b t i)=p) (hac : ∀ t,(∑ i,a t i*c t i)=p)
    (hbc : ∀ t,(∑ i,b t i*c t i)=p) (hq : ∀ t,(∑ i,a t i*b t i*c t i)=q) :
    (∑ i,∑ j,∑ k,if i ≠ j ∧ i ≠ k ∧ j ≠ k then ∑ t,a t i*b t j*c t k else 0)=
      (Fintype.card T : Scalar)*(512-24*p+2*q) := by
  have he (i j k : Omega) :
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k then ∑ t,a t i*b t j*c t k else 0)=
      ∑ t,if i ≠ j ∧ i ≠ k ∧ j ≠ k then a t i*b t j*c t k else 0 := by
    by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k <;> simp [h]
  simp_rw [he]
  rw [cubicTriangle_sum_comm_three]
  have ht (t : T) :
      (∑ i,∑ j,∑ k,if i ≠ j ∧ i ≠ k ∧ j ≠ k then a t i*b t j*c t k else 0)=
      8*8*8-p*8-p*8-p*8+2*q := by
    have hh := cubicTriangle_distinct_sum (a t) (b t) (c t)
    simp only [ha,hb,hc,hab,hac,hbc,hq] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> rfl

  simp_rw [ht]

  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

end Atlas.Fischer

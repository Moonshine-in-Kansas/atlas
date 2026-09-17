import Atlas.Algebra.IcosianDivision
set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

theorem icosian_scalar_of_commutes_I_J (q : IcosianQuaternion)
    (hi : q*icosianI=icosianI*q) (hj : q*icosianJ=icosianJ*q) :
    q=(q.re : IcosianQuaternion) := by
  have hk := congrArg QuaternionAlgebra.imJ hi
  have hji := congrArg QuaternionAlgebra.imK hi
  have hii := congrArg QuaternionAlgebra.imK hj
  simp [icosianI,icosianJ,Quaternion.imJ_mul,Quaternion.imK_mul] at hk hji hii
  have hK : q.imK=0 := CharZero.eq_neg_self_iff.mp hk
  have hJ : q.imJ=0 := CharZero.neg_eq_self_iff.mp hji
  have hI : q.imI=0 := CharZero.eq_neg_self_iff.mp hii
  ext <;> simp [hI,hJ,hK]

theorem icosian_norm_one_commutes_I_J (q : IcosianQuaternion)
    (hn : icosianNorm q=1) (hi : q*icosianI=icosianI*q)
    (hj : q*icosianJ=icosianJ*q) : q=1 ∨ q= -1 := by
  have he := icosian_scalar_of_commutes_I_J q hi hj
  have hs : q.re^2=1 := by
    rw [he] at hn
    simpa [icosianNorm,Quaternion.normSq,pow_two] using hn
  rcases sq_eq_one_iff.mp hs with h | h
  · left; rw [he,h]; rfl
  · right; rw [he,h]; rfl

end Atlas.Algebra

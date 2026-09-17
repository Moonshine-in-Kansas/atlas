import Atlas.Algebra.BinaryQuadraticNormalization

namespace Atlas.Algebra
open Atlas.Codes

/-- The actual six off-diagonal coefficients of the polar form. -/
def binaryAlternatingFour (c : Fin 11 → Bit) (s t : BinaryFour) : Bit :=
  c 5*(s 0*t 1+s 1*t 0)+c 6*(s 0*t 2+s 2*t 0)+c 7*(s 0*t 3+s 3*t 0)+
  c 8*(s 1*t 2+s 2*t 1)+c 9*(s 1*t 3+s 3*t 1)+c 10*(s 2*t 3+s 3*t 2)

def binaryQuadraticPfaffian (c : Fin 11 → Bit) : Bit := c 5*c 10+c 6*c 9+c 7*c 8

set_option maxHeartbeats 1000000 in
theorem binaryNormalizedQuadratic_polar (c : Fin 11 → Bit) (s t : BinaryFour) :
    (binaryNormalizedQuadratic c).polarBilin s t=binaryAlternatingFour c s t := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    binaryNormalizedQuadratic_apply,sub_eq_add_neg,CharTwo.neg_eq]
  simp [binaryQuadraticEvaluation,binaryQuadraticMonomials,Fin.sum_univ_succ,
    binaryAlternatingFour,Pi.add_apply]
  ring_nf
  simp only [show (2 : Bit)=0 from rfl,show (4 : Bit)=0 from rfl,show (6 : Bit)=0 from rfl,mul_zero,zero_add,add_zero]

end Atlas.Algebra

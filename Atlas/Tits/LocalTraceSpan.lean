import Atlas.Tits.LocalTranslationWords

namespace Atlas.Tits
open Atlas.Rudvalis
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The candidate row action of n; its identification with the group action
is a separate obligation. -/
def localRowMatrix : BinaryMatrix := !![1,1,1; 1,0,1; 0,0,1]

def pointParamMatrix (v : Fin 7 → Bit) : BinaryMatrix :=
  !![v 0,v 1,v 1; v 2,v 3,v 4; v 5,v 6,v 3+v 4+v 6]

def localMatrixDifference (M : BinaryMatrix) : BinaryMatrix :=
  localRowMatrix * M * localRowMatrix ^ 2 - M

def traceZeroParamMatrix (v : Fin 6 → Bit) : BinaryMatrix :=
  pointParamMatrix ![v 2+v 5,v 0,v 1,v 2,v 3,v 4,v 5]

def pointParamBasis (i : Fin 7) : BinaryMatrix :=
  pointParamMatrix (fun j => if i=j then 1 else 0)

theorem localRowMatrix_cube : localRowMatrix ^ 3 = 1 := by decide +kernel

theorem local_trace_zero_span_certificate (v : Fin 6 → Bit) :
    traceZeroParamMatrix v =
      (v 2+v 3) • (1 : BinaryMatrix) +
      (v 0+v 1+v 3+v 4+v 5) • uTranslationMatrix +
      (v 0+v 4) • localMatrixDifference (pointParamBasis 0) +
      (v 0+v 3) • localMatrixDifference (pointParamBasis 1) +
      v 5 • localMatrixDifference (pointParamBasis 5) +
      (v 0+v 1+v 3) • localMatrixDifference (pointParamBasis 6) := by
  decide +kernel +revert

theorem traceZeroParam_constraints (v : Fin 6 → Bit) :
    pointMatrixConstraints (traceZeroParamMatrix v) = 0 ∧
      pointTraceRaw (traceZeroParamMatrix v) = 0 := by
  decide +kernel +revert

theorem traceZeroParam_reconstruct (M : pointMatrixSpace) (ht : pointTrace M = 0) :
    traceZeroParamMatrix ![M.val 0 1, M.val 1 0, M.val 1 1, M.val 1 2,
      M.val 2 0, M.val 2 1] = M.val := by
  have h0 := congrArg (fun w : Fin 2 → Bit => w 0) M.prop
  have h1 := congrArg (fun w : Fin 2 → Bit => w 1) M.prop
  simp [pointMatrixSpace, pointMatrixConstraints] at h0 h1
  change M.val 0 0 + M.val 1 1 + M.val 2 1 = 0 at ht
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceZeroParamMatrix, pointParamMatrix]
  · linear_combination (norm := ring_nf) ht
    simp only [show (2 : Bit) = 0 by decide, mul_zero, zero_mul, neg_zero, add_zero, zero_add, sub_self]
  · linear_combination (norm := ring_nf) h0
    simp only [show (2 : Bit) = 0 by decide, mul_zero, zero_mul, neg_zero, add_zero, zero_add, sub_self]
  · linear_combination (norm := ring_nf) h1
    simp only [show (2 : Bit) = 0 by decide, mul_zero, zero_mul, neg_zero, add_zero, zero_add, sub_self]

end Atlas.Tits

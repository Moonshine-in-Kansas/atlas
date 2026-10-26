import Atlas.Algebra.SplitOctonion.NormComposition
import Atlas.LinearAlgebra.DotProductFiber
import Mathlib.Tactic

/-! Eight integral sparse elimination charts for octonion annihilators. The tables
are candidate formulas; the identities below are ring proofs of those formulas,
not imported computational certificates. -/
namespace Atlas.SplitOctonion.Annihilator
open scoped BigOperators
abbrev Parameters (F : Type*) := Fin 4 → F
variable {F : Type*} [CommRing F]

def leftFree : Fin 8 → Fin 4 → Fin 8 :=
  ![![0,1,2,4],
    ![0,1,3,5],
    ![0,2,3,6],
    ![0,4,5,6],
    ![1,2,3,7],
    ![1,4,5,7],
    ![2,4,6,7],
    ![3,5,6,7]]

def rightFree : Fin 8 → Fin 4 → Fin 8 :=
  ![![0,1,2,3],
    ![0,1,4,5],
    ![0,2,4,6],
    ![1,2,4,7],
    ![0,3,5,6],
    ![1,3,5,7],
    ![2,3,6,7],
    ![4,5,6,7]]

def leftNumerator (B : Carrier F) (a : Parameters F) : Fin 8 → Carrier F :=
  ![![B 0*a 0,B 0*a 1,B 0*a 2,- B 4*a 0 + B 2*a 1 - B 1*a 2,B 0*a 3,B 5*a 0 + B 3*a 1 + B 1*a 3,B 6*a 0 - B 3*a 2 - B 2*a 3,- B 6*a 1 - B 5*a 2 + B 4*a 3],
    ![B 1*a 0,B 1*a 1,- B 4*a 0 + B 2*a 1 - B 0*a 2,B 1*a 2,- B 5*a 0 - B 3*a 1 + B 0*a 3,B 1*a 3,- B 7*a 0 + B 3*a 2 - B 2*a 3,B 7*a 1 + B 5*a 2 + B 4*a 3],
    ![B 2*a 0,B 4*a 0 + B 1*a 1 + B 0*a 2,B 2*a 1,B 2*a 2,B 6*a 0 - B 3*a 1 - B 0*a 3,- B 7*a 0 + B 3*a 2 - B 1*a 3,B 2*a 3,B 7*a 1 - B 6*a 2 - B 4*a 3],
    ![B 3*a 0,- B 5*a 0 - B 1*a 1 + B 0*a 2,B 6*a 0 - B 2*a 1 - B 0*a 3,B 7*a 0 + B 2*a 2 + B 1*a 3,B 3*a 1,B 3*a 2,B 3*a 3,- B 7*a 1 - B 6*a 2 + B 5*a 3],
    ![B 2*a 0 - B 1*a 1 - B 0*a 2,B 4*a 0,B 4*a 1,B 4*a 2,B 6*a 0 + B 5*a 1 + B 0*a 3,- B 7*a 0 - B 5*a 2 + B 1*a 3,B 7*a 1 - B 6*a 2 - B 2*a 3,B 4*a 3],
    ![- B 3*a 0 - B 1*a 1 + B 0*a 2,B 5*a 0,- B 6*a 0 + B 4*a 1 - B 0*a 3,- B 7*a 0 - B 4*a 2 + B 1*a 3,B 5*a 1,B 5*a 2,B 7*a 1 + B 6*a 2 + B 3*a 3,B 5*a 3],
    ![B 3*a 0 + B 2*a 1 + B 0*a 2,- B 5*a 0 + B 4*a 1 - B 0*a 3,B 6*a 0,B 7*a 0 - B 4*a 2 - B 2*a 3,B 6*a 1,- B 7*a 1 + B 5*a 2 - B 3*a 3,B 6*a 2,B 6*a 3],
    ![B 3*a 0 - B 2*a 1 - B 1*a 2,- B 5*a 0 - B 4*a 1 + B 1*a 3,B 6*a 0 + B 4*a 2 + B 2*a 3,B 7*a 0,- B 6*a 1 + B 5*a 2 - B 3*a 3,B 7*a 1,B 7*a 2,B 7*a 3]]

def rightNumerator (B : Carrier F) (c : Parameters F) : Fin 8 → Carrier F :=
  ![![B 0*c 0,B 0*c 1,B 0*c 2,B 0*c 3,B 1*c 2 - B 2*c 1 - B 3*c 0,- B 1*c 3 - B 4*c 1 + B 5*c 0,B 2*c 3 + B 4*c 2 + B 6*c 0,B 3*c 3 - B 5*c 2 - B 6*c 1],
    ![B 1*c 0,B 1*c 1,B 0*c 2 + B 2*c 1 + B 3*c 0,- B 0*c 3 - B 4*c 1 + B 5*c 0,B 1*c 2,B 1*c 3,- B 2*c 3 + B 4*c 2 - B 7*c 0,- B 3*c 3 - B 5*c 2 + B 7*c 1],
    ![B 2*c 0,- B 0*c 2 + B 1*c 1 - B 3*c 0,B 2*c 1,B 0*c 3 - B 4*c 1 - B 6*c 0,B 2*c 2,- B 1*c 3 + B 4*c 2 - B 7*c 0,B 2*c 3,B 3*c 3 + B 6*c 2 + B 7*c 1],
    ![- B 0*c 2 + B 1*c 1 - B 2*c 0,B 3*c 0,B 3*c 1,B 0*c 3 + B 5*c 1 + B 6*c 0,B 3*c 2,- B 1*c 3 - B 5*c 2 + B 7*c 0,B 2*c 3 - B 6*c 2 - B 7*c 1,B 3*c 3],
    ![B 4*c 0,- B 0*c 2 - B 1*c 1 + B 5*c 0,B 0*c 3 - B 2*c 1 - B 6*c 0,B 4*c 1,B 1*c 3 + B 2*c 2 + B 7*c 0,B 4*c 2,B 4*c 3,- B 5*c 3 + B 6*c 2 - B 7*c 1],
    ![B 0*c 2 + B 1*c 1 + B 4*c 0,B 5*c 0,- B 0*c 3 + B 3*c 1 - B 6*c 0,B 5*c 1,- B 1*c 3 - B 3*c 2 + B 7*c 0,B 5*c 2,- B 4*c 3 + B 6*c 2 - B 7*c 1,B 5*c 3],
    ![B 0*c 2 - B 2*c 1 - B 4*c 0,- B 0*c 3 + B 3*c 1 - B 5*c 0,B 6*c 0,B 6*c 1,B 2*c 3 - B 3*c 2 - B 7*c 0,B 4*c 3 + B 5*c 2 + B 7*c 1,B 6*c 2,B 6*c 3],
    ![- B 1*c 2 - B 2*c 1 + B 4*c 0,B 1*c 3 + B 3*c 1 + B 5*c 0,B 2*c 3 - B 3*c 2 - B 6*c 0,- B 4*c 3 - B 5*c 2 + B 6*c 1,B 7*c 0,B 7*c 1,B 7*c 2,B 7*c 3]]

def leftCorrection (w : Carrier F) : Fin 8 → Carrier F :=
  ![![0,0,0,w 0,0,- w 1,w 2,- w 4],
    ![0,0,w 0,0,w 1,0,- w 3,- w 5],
    ![0,- w 0,0,0,w 2,- w 3,0,w 6],
    ![0,w 1,w 2,w 3,0,0,0,w 7],
    ![w 0,0,0,0,w 4,w 5,w 6,0],
    ![w 1,0,- w 4,w 5,0,0,- w 7,0],
    ![- w 2,- w 4,0,w 6,0,w 7,0,0],
    ![- w 3,w 5,- w 6,0,w 7,0,0,0]]

def rightCorrection (w : Carrier F) : Fin 8 → Carrier F :=
  ![![0,0,0,0,w 0,w 1,- w 2,- w 3],
    ![0,0,- w 0,w 1,0,0,- w 4,w 5],
    ![0,w 0,0,w 2,0,- w 4,0,- w 6],
    ![w 0,0,0,w 3,0,w 5,w 6,0],
    ![0,w 1,w 2,0,w 4,0,0,w 7],
    ![- w 1,0,- w 3,0,w 5,0,w 7,0],
    ![w 2,- w 3,0,0,w 6,- w 7,0,0],
    ![- w 4,- w 5,w 6,w 7,0,0,0,0]]

def leftResidual (a : Parameters F) : Fin 8 → Carrier F :=
  ![![0,0,0,- a 0,0,a 1,- a 2,a 3],
    ![0,0,- a 0,0,- a 1,0,a 2,a 3],
    ![0,a 0,0,0,- a 1,a 2,0,- a 3],
    ![a 0,0,0,0,a 1,a 2,a 3,0],
    ![0,a 0,a 1,a 2,0,0,0,a 3],
    ![- a 0,0,a 1,- a 2,0,0,a 3,0],
    ![a 0,a 1,0,- a 2,0,- a 3,0,0],
    ![a 0,- a 1,a 2,0,- a 3,0,0,0]]

def rightResidual (c : Parameters F) : Fin 8 → Carrier F :=
  ![![0,0,0,0,- c 0,- c 1,c 2,c 3],
    ![0,0,c 0,- c 1,0,0,c 2,- c 3],
    ![0,- c 0,0,- c 1,0,c 2,0,c 3],
    ![0,c 0,c 1,0,c 2,0,0,c 3],
    ![c 0,0,0,c 1,0,c 2,c 3,0],
    ![c 0,0,c 1,0,- c 2,0,- c 3,0],
    ![- c 0,c 1,0,0,- c 2,c 3,0,0],
    ![c 0,c 1,- c 2,- c 3,0,0,0,0]]

def pairCoefficients (a : Parameters F) : Fin 8 → Parameters F :=
  ![![a 3,- a 2,a 1,a 0],
    ![a 3,a 2,a 1,- a 0],
    ![- a 3,a 2,a 1,a 0],
    ![- a 3,- a 2,a 1,- a 0],
    ![- a 3,a 2,- a 1,- a 0],
    ![a 3,a 2,a 1,- a 0],
    ![- a 3,a 2,a 1,a 0],
    ![a 3,a 2,- a 1,a 0]]

def productResidual (a c : Parameters F) : Fin 8 → Carrier F :=
  ![![0,0,0,0,0,0,0,- a 0*c 3 - a 1*c 2 + a 2*c 1 - a 3*c 0],
    ![0,0,0,0,0,0,a 0*c 3 - a 1*c 2 - a 2*c 1 - a 3*c 0,0],
    ![0,0,0,0,0,- a 0*c 3 - a 1*c 2 - a 2*c 1 + a 3*c 0,0,0],
    ![0,0,0,a 0*c 3 - a 1*c 2 + a 2*c 1 + a 3*c 0,0,0,0,0],
    ![0,0,0,0,a 0*c 3 + a 1*c 2 - a 2*c 1 + a 3*c 0,0,0,0],
    ![0,0,a 0*c 3 - a 1*c 2 - a 2*c 1 - a 3*c 0,0,0,0,0,0],
    ![0,- a 0*c 3 - a 1*c 2 - a 2*c 1 + a 3*c 0,0,0,0,0,0,0],
    ![- a 0*c 3 + a 1*c 2 - a 2*c 1 - a 3*c 0,0,0,0,0,0,0,0]]

def pivotSign : Fin 8 → F := ![-1,-1,-1,1,1,-1,-1,-1]

theorem leftNumerator_free (B : Carrier F) (a : Parameters F) (i : Fin 8) (j : Fin 4) :
    leftNumerator B a i (leftFree i j)=B i*a j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem rightNumerator_free (B : Carrier F) (c : Parameters F) (i : Fin 8) (j : Fin 4) :
    rightNumerator B c i (rightFree i j)=B i*c j := by
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 1600000 in
theorem leftNumerator_product (B : Carrier F) (a : Parameters F) (i : Fin 8) :
    mul (leftNumerator B a i) B=norm B • leftResidual a i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [leftNumerator,leftResidual,mul,norm,Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
theorem rightNumerator_product (B : Carrier F) (c : Parameters F) (i : Fin 8) :
    mul B (rightNumerator B c i)=norm B • rightResidual c i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [rightNumerator,rightResidual,mul,norm,Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
theorem leftNumerator_reconstruct (A B : Carrier F) (i : Fin 8) :
    leftNumerator B (fun j=>A (leftFree i j)) i=B i • A-leftCorrection (mul A B) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [leftNumerator,leftFree,leftCorrection,mul,Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
theorem rightNumerator_reconstruct (B C : Carrier F) (i : Fin 8) :
    rightNumerator B (fun j=>C (rightFree i j)) i=B i • C-rightCorrection (mul B C) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [rightNumerator,rightFree,rightCorrection,mul,Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
/-- Product of the two numerator charts factors through one nondegenerate pairing
modulo the norm equation; this is the uniform common-annihilator identity. -/
-- Eight sparse cubic-coordinate checks, valid over every commutative ring.
theorem numerator_pairing (B : Carrier F) (a c : Parameters F) (i : Fin 8) :
    mul (rightNumerator B c i) (leftNumerator B a i)=
      (pivotSign i*B i*(∑ j, pairCoefficients a i j * c j)) • conjugate B+
        norm B • productResidual a c i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [leftNumerator,rightNumerator,pivotSign,pairCoefficients,productResidual,
      Fin.sum_univ_succ,mul,norm,conjugate,trace,unit,
      Matrix.vecHead,Matrix.vecTail] <;> ring

theorem pairCoefficients_eq_zero (a : Parameters F) (i : Fin 8) : pairCoefficients a i=0 ↔ a=0 := by
  fin_cases i <;> simp [pairCoefficients,funext_iff,Fin.forall_fin_succ] <;> tauto

end Atlas.SplitOctonion.Annihilator

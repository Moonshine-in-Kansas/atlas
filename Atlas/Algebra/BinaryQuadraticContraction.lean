import Atlas.Algebra.BinaryFourSymbolicSum
import Atlas.Algebra.BinaryQuadraticPolarCoefficients
import Atlas.Algebra.BinaryBilinearContraction

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators


def binaryQuadraticContractionBilin (c : Fin 11 → Bit) :=
  binaryBilinearContraction (binaryQuadraticEvaluation c) (binaryNormalizedQuadratic c).polarBilin

theorem binaryQuadraticContractionBilin_apply (c : Fin 11 → Bit) (s t : BinaryFour) :
    binaryQuadraticContractionBilin c s t =
      ∑ v, binaryQuadraticEvaluation c v * binaryAlternatingFour c s v * binaryAlternatingFour c t v := by
  change (∑ v, binaryQuadraticEvaluation c v * (binaryNormalizedQuadratic c).polarBilin s v *
    (binaryNormalizedQuadratic c).polarBilin t v)=_
  simp only [binaryNormalizedQuadratic_polar]

def binaryQuadraticContractionEntry (c : Fin 11 → Bit) (i j : Fin 4) : Prop :=
  (∑ v, binaryQuadraticEvaluation c v * binaryAlternatingFour c (Pi.single i 1) v *
    binaryAlternatingFour c (Pi.single j 1) v) =
      binaryQuadraticPfaffian c * binaryAlternatingFour c (Pi.single i 1) (Pi.single j 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem binaryQuadraticContraction_row0 (c : Fin 11 → Bit) (j : Fin 4) :
    binaryQuadraticContractionEntry c 0 j := by
  fin_cases j <;> unfold binaryQuadraticContractionEntry <;> rw [binaryFour_sum] <;>
    simp [binaryQuadraticEvaluation,binaryQuadraticMonomials,Fin.sum_univ_succ,
      binaryAlternatingFour,binaryQuadraticPfaffian,Pi.single_apply] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 from rfl,show (4 : Bit)=0 from rfl,
      show (6 : Bit)=0 from rfl,show (8 : Bit)=0 from rfl,show (10 : Bit)=0 from rfl,
      show (12 : Bit)=0 from rfl,show (14 : Bit)=0 from rfl,show (16 : Bit)=0 from rfl,
      show (3 : Bit)=1 from rfl,mul_one,mul_zero,zero_add,add_zero]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem binaryQuadraticContraction_row1 (c : Fin 11 → Bit) (j : Fin 4) :
    binaryQuadraticContractionEntry c 1 j := by
  fin_cases j <;> unfold binaryQuadraticContractionEntry <;> rw [binaryFour_sum] <;>
    simp [binaryQuadraticEvaluation,binaryQuadraticMonomials,Fin.sum_univ_succ,
      binaryAlternatingFour,binaryQuadraticPfaffian,Pi.single_apply] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 from rfl,show (4 : Bit)=0 from rfl,
      show (6 : Bit)=0 from rfl,show (8 : Bit)=0 from rfl,show (10 : Bit)=0 from rfl,
      show (12 : Bit)=0 from rfl,show (14 : Bit)=0 from rfl,show (16 : Bit)=0 from rfl,
      show (3 : Bit)=1 from rfl,mul_one,mul_zero,zero_add,add_zero]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem binaryQuadraticContraction_row2 (c : Fin 11 → Bit) (j : Fin 4) :
    binaryQuadraticContractionEntry c 2 j := by
  fin_cases j <;> unfold binaryQuadraticContractionEntry <;> rw [binaryFour_sum] <;>
    simp [binaryQuadraticEvaluation,binaryQuadraticMonomials,Fin.sum_univ_succ,
      binaryAlternatingFour,binaryQuadraticPfaffian,Pi.single_apply] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 from rfl,show (4 : Bit)=0 from rfl,
      show (6 : Bit)=0 from rfl,show (8 : Bit)=0 from rfl,show (10 : Bit)=0 from rfl,
      show (12 : Bit)=0 from rfl,show (14 : Bit)=0 from rfl,show (16 : Bit)=0 from rfl,
      show (3 : Bit)=1 from rfl,mul_one,mul_zero,zero_add,add_zero]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem binaryQuadraticContraction_row3 (c : Fin 11 → Bit) (j : Fin 4) :
    binaryQuadraticContractionEntry c 3 j := by
  fin_cases j <;> unfold binaryQuadraticContractionEntry <;> rw [binaryFour_sum] <;>
    simp [binaryQuadraticEvaluation,binaryQuadraticMonomials,Fin.sum_univ_succ,
      binaryAlternatingFour,binaryQuadraticPfaffian,Pi.single_apply] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 from rfl,show (4 : Bit)=0 from rfl,
      show (6 : Bit)=0 from rfl,show (8 : Bit)=0 from rfl,show (10 : Bit)=0 from rfl,
      show (12 : Bit)=0 from rfl,show (14 : Bit)=0 from rfl,show (16 : Bit)=0 from rfl,
      show (3 : Bit)=1 from rfl,mul_one,mul_zero,zero_add,add_zero]

/-- Bilinearity reduces the symbolic identity to the sixteen basis pairs. -/
theorem binaryQuadraticContractionBilin_eq (c : Fin 11 → Bit) :
    binaryQuadraticContractionBilin c = binaryQuadraticPfaffian c • (binaryNormalizedQuadratic c).polarBilin := by
  apply binaryBilinear_eq_of_basis
  intro i j
  rw [binaryQuadraticContractionBilin_apply]
  simp only [LinearMap.smul_apply,smul_eq_mul,binaryNormalizedQuadratic_polar]
  change binaryQuadraticContractionEntry c i j
  fin_cases i
  · exact binaryQuadraticContraction_row0 c j
  · exact binaryQuadraticContraction_row1 c j
  · exact binaryQuadraticContraction_row2 c j
  · exact binaryQuadraticContraction_row3 c j

/-- The four-variable contraction, uniformly in the original polynomial and
both vector arguments. -/
theorem binaryQuadraticEvaluation_polar_contraction (c : Fin 11 → Bit) (s t : BinaryFour) :
    (∑ v, binaryQuadraticEvaluation c v * binaryAlternatingFour c s v *
      binaryAlternatingFour c t v) =
        binaryQuadraticPfaffian c * binaryAlternatingFour c s t := by
  rw [← binaryQuadraticContractionBilin_apply,binaryQuadraticContractionBilin_eq]
  simp only [LinearMap.smul_apply,smul_eq_mul,binaryNormalizedQuadratic_polar]

end Atlas.Algebra

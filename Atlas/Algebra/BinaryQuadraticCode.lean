import Atlas.Codes.BinaryLift
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

abbrev BinaryFour := Fin 4 → Bit
abbrev BinaryFourWord := BinaryFour → Bit

/-- The eleven square-free monomials of total degree at most two. -/
def binaryQuadraticMonomials (v : BinaryFour) : Fin 11 → Bit :=
  ![1,v 0,v 1,v 2,v 3,v 0*v 1,v 0*v 2,v 0*v 3,v 1*v 2,v 1*v 3,v 2*v 3]

/-- Literal evaluation of the constant, four linear, and six quadratic coefficients. -/
def binaryQuadraticEvaluation : (Fin 11 → Bit) →ₗ[Bit] BinaryFourWord where
  toFun c v := ∑ k, c k * binaryQuadraticMonomials v k
  map_add' c d := by funext v; simp [add_mul,Finset.sum_add_distrib]
  map_smul' r c := by
    funext v
    simp [Finset.mul_sum,mul_assoc]

/-- Coefficients recovered from the origin, unit points, and their pair sums.
This is an explicit interpolation operation on the same sixteen coordinates. -/
def binaryQuadraticRecover (w : BinaryFourWord) : Fin 11 → Bit :=
  ![w ![0,0,0,0],
    w ![1,0,0,0]+w ![0,0,0,0],
    w ![0,1,0,0]+w ![0,0,0,0],
    w ![0,0,1,0]+w ![0,0,0,0],
    w ![0,0,0,1]+w ![0,0,0,0],
    w ![1,1,0,0]+w ![1,0,0,0]+w ![0,1,0,0]+w ![0,0,0,0],
    w ![1,0,1,0]+w ![1,0,0,0]+w ![0,0,1,0]+w ![0,0,0,0],
    w ![1,0,0,1]+w ![1,0,0,0]+w ![0,0,0,1]+w ![0,0,0,0],
    w ![0,1,1,0]+w ![0,1,0,0]+w ![0,0,1,0]+w ![0,0,0,0],
    w ![0,1,0,1]+w ![0,1,0,0]+w ![0,0,0,1]+w ![0,0,0,0],
    w ![0,0,1,1]+w ![0,0,1,0]+w ![0,0,0,1]+w ![0,0,0,0]]

set_option maxHeartbeats 1000000 in
theorem binaryQuadraticRecover_evaluation (c : Fin 11 → Bit) :
    binaryQuadraticRecover (binaryQuadraticEvaluation c) = c := by
  funext k
  fin_cases k <;>
    simp [binaryQuadraticRecover,binaryQuadraticEvaluation,binaryQuadraticMonomials,
      Fin.sum_univ_succ] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 from rfl,show (4 : Bit)=0 from rfl,
      mul_zero,add_zero,zero_add]

theorem binaryQuadraticEvaluation_injective : Function.Injective binaryQuadraticEvaluation :=
  Function.LeftInverse.injective binaryQuadraticRecover_evaluation

/-- RM(2,4), defined by actual monomial evaluation rather than numerical parameters. -/
def binaryQuadraticCode : Submodule Bit BinaryFourWord := binaryQuadraticEvaluation.range

noncomputable def binaryQuadraticCodeEquiv : (Fin 11 → Bit) ≃ₗ[Bit] binaryQuadraticCode :=
  LinearEquiv.ofInjective binaryQuadraticEvaluation binaryQuadraticEvaluation_injective

theorem binaryQuadraticCode_finrank : Module.finrank Bit binaryQuadraticCode = 11 := by
  rw [← binaryQuadraticCodeEquiv.finrank_eq]
  simp

end Atlas.Algebra

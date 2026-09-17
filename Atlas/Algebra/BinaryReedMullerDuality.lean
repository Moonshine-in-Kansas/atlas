import Atlas.Algebra.BinaryQuadraticCode
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

/-- The constant and four coordinate monomials. -/
def binaryAffineMonomials (v : BinaryFour) : Fin 5 → Bit := ![1,v 0,v 1,v 2,v 3]

def binaryAffineEvaluation : (Fin 5 → Bit) →ₗ[Bit] BinaryFourWord where
  toFun c v := ∑ k, c k * binaryAffineMonomials v k
  map_add' c d := by funext v; simp [add_mul,Finset.sum_add_distrib]
  map_smul' r c := by funext v; simp [Finset.mul_sum,mul_assoc]

def binaryAffineRecover (w : BinaryFourWord) : Fin 5 → Bit :=
  ![w ![0,0,0,0],w ![1,0,0,0]+w ![0,0,0,0],
    w ![0,1,0,0]+w ![0,0,0,0],w ![0,0,1,0]+w ![0,0,0,0],
    w ![0,0,0,1]+w ![0,0,0,0]]

theorem binaryAffineRecover_evaluation (c : Fin 5 → Bit) :
    binaryAffineRecover (binaryAffineEvaluation c) = c := by
  funext k
  fin_cases k <;>
    simp [binaryAffineRecover,binaryAffineEvaluation,binaryAffineMonomials,
      Fin.sum_univ_succ] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 from rfl,mul_zero,add_zero,zero_add]

theorem binaryAffineEvaluation_injective : Function.Injective binaryAffineEvaluation :=
  Function.LeftInverse.injective binaryAffineRecover_evaluation

def binaryAffineCode : Submodule Bit BinaryFourWord := binaryAffineEvaluation.range

noncomputable def binaryAffineCodeEquiv : (Fin 5 → Bit) ≃ₗ[Bit] binaryAffineCode :=
  LinearEquiv.ofInjective binaryAffineEvaluation binaryAffineEvaluation_injective

theorem binaryAffineCode_finrank : Module.finrank Bit binaryAffineCode = 5 := by
  rw [← binaryAffineCodeEquiv.finrank_eq]
  simp

theorem binaryQuadraticEvaluation_sum (c : Fin 11 → Bit) :
    binaryQuadraticEvaluation c = ∑ k, c k • (fun v => binaryQuadraticMonomials v k) := by
  funext v
  simp [binaryQuadraticEvaluation,Finset.sum_apply]

theorem binaryAffineEvaluation_sum (c : Fin 5 → Bit) :
    binaryAffineEvaluation c = ∑ k, c k • (fun v => binaryAffineMonomials v k) := by
  funext v
  simp [binaryAffineEvaluation,Finset.sum_apply]

/-- The bounded 11-by-5 monomial pairing, each a sum over precisely sixteen
binary points. Coefficients and arbitrary words are not enumerated. -/
theorem binaryQuadraticAffine_monomial_dot : ∀ (i : Fin 11) (j : Fin 5),
    binaryDot (fun v => binaryQuadraticMonomials v i)
      (fun v => binaryAffineMonomials v j) = 0 := by
  decide +kernel

theorem binaryQuadraticAffine_dot (c : Fin 11 → Bit) (d : Fin 5 → Bit) :
    binaryDot (binaryQuadraticEvaluation c) (binaryAffineEvaluation d) = 0 := by
  rw [binaryQuadraticEvaluation_sum,binaryAffineEvaluation_sum]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
    binaryQuadraticAffine_monomial_dot,mul_zero,Finset.sum_const_zero]

theorem binaryQuadraticCode_le_affine_orthogonal :
    binaryQuadraticCode ≤ binaryDot.orthogonal binaryAffineCode := by
  rintro w ⟨c,rfl⟩ z ⟨d,rfl⟩
  rw [binaryDot_symmetric]
  exact binaryQuadraticAffine_dot c d

/-- Reed--Muller duality is established on the literal function coordinates:
the quadratic evaluation code is exactly the affine code's orthogonal complement. -/
theorem binaryQuadraticCode_eq_affine_orthogonal :
    binaryQuadraticCode = binaryDot.orthogonal binaryAffineCode := by
  apply Submodule.eq_of_le_of_finrank_le binaryQuadraticCode_le_affine_orthogonal
  rw [LinearMap.BilinForm.finrank_orthogonal binaryDot_nondegenerate,
    binaryAffineCode_finrank,binaryQuadraticCode_finrank]
  simp [BinaryFourWord,BinaryFour,Module.finrank_pi,Bit,ZMod.card]

end Atlas.Algebra

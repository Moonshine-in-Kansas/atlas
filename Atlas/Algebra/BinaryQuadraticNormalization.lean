import Atlas.Algebra.BinaryAffineFunctions
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

/-- The ten normalized quadratic monomials. Over F₂ the four diagonal
quadratic monomials are the ordinary coordinate linear functions. -/
def binaryNormalizedMonomials : Fin 10 → QuadraticMap Bit BinaryFour Bit :=
  ![QuadraticMap.proj 0 0,QuadraticMap.proj 1 1,QuadraticMap.proj 2 2,QuadraticMap.proj 3 3,
    QuadraticMap.proj 0 1,QuadraticMap.proj 0 2,QuadraticMap.proj 0 3,
    QuadraticMap.proj 1 2,QuadraticMap.proj 1 3,QuadraticMap.proj 2 3]

def binaryNormalizedQuadratic (c : Fin 11 → Bit) : QuadraticMap Bit BinaryFour Bit :=
  ∑ i : Fin 10, c i.succ • binaryNormalizedMonomials i

set_option maxHeartbeats 1000000 in
theorem binaryNormalizedQuadratic_apply (c : Fin 11 → Bit) (v : BinaryFour) :
    binaryNormalizedQuadratic c v = binaryQuadraticEvaluation c v+c 0 := by
  have hb : ∀ b : Bit, b*b=b := by decide
  simp [binaryNormalizedQuadratic,binaryNormalizedMonomials,QuadraticMap.proj,
    QuadraticMap.linMulLin,binaryQuadraticEvaluation,binaryQuadraticMonomials,
    Fin.sum_univ_succ,hb]
  ring_nf
  simp only [show (2 : Bit)=0 from rfl,mul_zero,add_zero,zero_add]

theorem binaryQuadraticEvaluation_zero (c : Fin 11 → Bit) :
    binaryQuadraticEvaluation c 0=c 0 := by
  simp [binaryQuadraticEvaluation,binaryQuadraticMonomials,Fin.sum_univ_succ]

/-- The actual normalized quadratic map attached to a literal quadratic word. -/
noncomputable def binaryQuadraticWordForm (w : binaryQuadraticCode) :
    QuadraticMap Bit BinaryFour Bit :=
  binaryNormalizedQuadratic (binaryQuadraticCodeEquiv.symm w)

/-- Removing the constant is explicit; the original coordinate function is retained. -/
theorem binaryQuadraticWordForm_apply (w : binaryQuadraticCode) (v : BinaryFour) :
    binaryQuadraticWordForm w v=w.val v+w.val 0 := by
  rw [binaryQuadraticWordForm,binaryNormalizedQuadratic_apply]
  have h : binaryQuadraticEvaluation (binaryQuadraticCodeEquiv.symm w)=w.val :=
    congrArg Subtype.val (binaryQuadraticCodeEquiv.apply_symm_apply w)
  rw [← binaryQuadraticEvaluation_zero (binaryQuadraticCodeEquiv.symm w),h]

/-- Addition of an affine function leaves the actual polar bilinear map unchanged. -/
theorem binaryQuadraticWordForm_polar_eq_of_affine (w z : binaryQuadraticCode)
    (h : w.val+z.val ∈ binaryAffineCode) :
    (binaryQuadraticWordForm w).polarBilin=(binaryQuadraticWordForm z).polarBilin := by
  obtain ⟨a,l,hl⟩ := (binaryAffineCode_mem_iff _).mp h
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  have h0 := hl 0
  have hu := hl u
  have hv := hl v
  have huv := hl (u+v)
  simp only [Pi.add_apply,map_zero,add_zero] at h0
  simp only [Pi.add_apply,map_add] at hu hv huv
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    binaryQuadraticWordForm_apply,sub_eq_add_neg,CharTwo.neg_eq]
  have he : (w.val (u+v)+w.val 0+w.val u+w.val 0+w.val v+w.val 0)+
      (z.val (u+v)+z.val 0+z.val u+z.val 0+z.val v+z.val 0)=0 := by
    calc
      _ = (w.val (u+v)+z.val (u+v))+(w.val u+z.val u)+(w.val v+z.val v)+
        ((w.val 0+z.val 0)+(w.val 0+z.val 0)+(w.val 0+z.val 0)) := by abel
      _ = 0 := by rw [huv,hu,hv,h0]; ring_nf; simp only [show (2 : Bit)=0 from rfl,
        show (6 : Bit)=0 from rfl,mul_zero,add_zero,zero_add]
  have hh := (eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _)
  simpa only [add_assoc] using hh

end Atlas.Algebra

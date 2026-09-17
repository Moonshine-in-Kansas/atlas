import Atlas.Lattices.EisensteinFourierMatrix
import Atlas.Conway.EisensteinPhaseIsometries
import Atlas.Lattices.EisensteinMonomial

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators QuadraticAlgebra Matrix

def eisensteinFusionInputWord : TernaryWord := ![0,1,2,0,0,0,0,0,2,2,1,1]
def eisensteinFusionOutputWord : TernaryWord := ![0,0,0,0,0,0,2,2,2,2,2,2]

theorem eisensteinFusionInput_mem : eisensteinFusionInputWord ∈ ternaryGolay := by
  have h : eisensteinFusionInputWord = ternaryEncoder (ternaryDecoder eisensteinFusionInputWord) := by
    decide +kernel
  rw [h]; exact ⟨_,rfl⟩

theorem eisensteinFusionOutput_mem : eisensteinFusionOutputWord ∈ ternaryGolay := by
  have h : eisensteinFusionOutputWord = ternaryEncoder (ternaryDecoder eisensteinFusionOutputWord) := by
    decide +kernel
  rw [h]; exact ⟨_,rfl⟩

def eisensteinFusionInput : ternaryGolay := ⟨eisensteinFusionInputWord,eisensteinFusionInput_mem⟩
def eisensteinFusionOutput : ternaryGolay := ⟨eisensteinFusionOutputWord,eisensteinFusionOutput_mem⟩

def eisensteinFusionPermutation : Equiv.Perm (Fin 12) where
  toFun := ![2,0,1,3,4,5,11,9,6,10,7,8]
  invFun := ![1,2,0,3,4,5,8,10,11,7,9,6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem eisensteinFusionPermutation_code_check : ∀ p : TernaryParameters,
    (fun i => ternaryEncoder p (eisensteinFusionPermutation.symm i)) =
      ternaryEncoder (ternaryDecoder (fun i => ternaryEncoder p (eisensteinFusionPermutation.symm i))) := by
  decide +kernel

theorem eisensteinFusionPermutation_mem : eisensteinFusionPermutation ∈ ternaryPureAutomorphism := by
  rintro w ⟨p,rfl⟩
  rw [eisensteinFusionPermutation_code_check]
  exact ⟨_,rfl⟩

theorem eisensteinFusionPermutation_ne_one : eisensteinFusionPermutation ≠ 1 := by
  intro h
  have hi := Equiv.congr_fun h 0
  norm_num [eisensteinFusionPermutation] at hi
  exact (by decide : (2 : Fin 12) ≠ 0) hi

def eisensteinFusionDiagonalMatrix (t : TernaryWord) :
    Matrix (Fin 12) (Fin 12) EisensteinRational :=
  Matrix.diagonal (fun i => eisensteinToRational (eisensteinPhase (t i)))

def eisensteinFusionMonomialMatrix : Matrix (Fin 12) (Fin 12) EisensteinRational := fun i j =>
  if j=eisensteinFusionPermutation.symm i then
    eisensteinToRational (eisensteinPhase (eisensteinFusionOutputWord i)) else 0

/-- The complete twelve-coordinate phase-to-permutation conjugation identity. -/
theorem eisensteinFourier_fusion_matrix :
    eisensteinFourierMatrix * eisensteinFusionDiagonalMatrix eisensteinFusionInputWord *
      eisensteinFourierMatrix.conjTranspose = eisensteinFusionMonomialMatrix := by
  decide +kernel

theorem eisensteinFusionInput_not_constant : eisensteinFusionInput ∉ ternaryConstants := by
  intro h
  obtain ⟨a,ha⟩ := (Submodule.mem_span_singleton.mp h)
  have h0 := congrFun (congrArg Subtype.val ha) 0
  have h1 := congrFun (congrArg Subtype.val ha) 1
  change a*1=0 at h0
  change a*1=1 at h1
  have : (0 : ZMod 3)=1 := h0.symm.trans h1
  exact zero_ne_one this

end Atlas.Conway

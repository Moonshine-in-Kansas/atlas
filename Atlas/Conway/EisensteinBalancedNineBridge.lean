import Atlas.Conway.EisensteinBalancedClassExhaustion

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

def eisensteinNineBridgePermutation : Equiv.Perm (Fin 12) where
  toFun := ![0,7,8,3,11,5,9,1,2,6,10,4]
  invFun := ![0,7,8,3,11,5,9,1,2,6,10,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem eisensteinNineBridgePermutation_mem :
    eisensteinNineBridgePermutation ∈ ternaryPureAutomorphism := by
  have hc : ∀ p : TernaryParameters,
      (fun i => ternaryEncoder p (eisensteinNineBridgePermutation.symm i)) =
        ternaryEncoder (ternaryDecoder (fun i => ternaryEncoder p (eisensteinNineBridgePermutation.symm i))) := by
    decide +kernel
  rintro w ⟨p,rfl⟩
  rw [hc]
  exact ⟨_,rfl⟩

def eisensteinNineBridgeCodePermutation : TernaryPureAutomorphism :=
  ⟨eisensteinNineBridgePermutation,eisensteinNineBridgePermutation_mem⟩

def eisensteinNineBridgePhaseWord : TernaryWord := ![0,1,1,2,1,1,2,1,2,1,0,0]

theorem eisensteinNineBridgePhase_mem : eisensteinNineBridgePhaseWord ∈ ternaryGolay := by
  have h : eisensteinNineBridgePhaseWord=ternaryEncoder (ternaryDecoder eisensteinNineBridgePhaseWord) := by
    decide +kernel
  rw [h]
  exact ⟨_,rfl⟩

def eisensteinNineBridgePhase : ternaryGolay := ⟨eisensteinNineBridgePhaseWord,eisensteinNineBridgePhase_mem⟩

def eisensteinNineBridgeLocal : eisensteinCoordinateFrameStabilizer :=
  eisensteinFrameFromParameters (false,eisensteinNineBridgePhase,eisensteinNineBridgeCodePermutation)

def eisensteinNineBridgeIsometry : eisensteinHermitianGroup :=
  eisensteinFourierIsometry*eisensteinNineBridgeLocal.val*eisensteinFourierIsometry

def eisensteinNineBridgeFrame : EisensteinFrame := eisensteinNineBridgeIsometry •
  eisensteinTriadFrame {0,1,7} eisensteinBalancedSourceBase_card 0

theorem eisensteinNineBridge_edge :
    ∃ F ∈ eisensteinBalancedFamily,eisensteinFourierIsometry • F=eisensteinNineBridgeFrame := by
  refine ⟨eisensteinNineBridgeLocal.val • eisensteinBalancedParameterFrame eisensteinFourierBalancedParameter,
    eisensteinBalancedFamily_invariant _ _ (eisensteinBalancedParameterFrame_mem _),?_⟩
  rw [← eisensteinFourier_triad_balanced]
  exact (mul_smul _ _ _).symm.trans (by rw [← mul_smul]; rfl)

end Atlas.Conway

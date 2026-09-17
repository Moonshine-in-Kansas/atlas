import Atlas.Conway.EisensteinTriadUnitOrbit
import Atlas.Conway.EisensteinBalancedFourier

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

private theorem unitFourier_phase_zero (x : EisensteinShell 6) :
    eisensteinCodePhaseShell 0 x = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [eisensteinCodePhaseShell_apply]
  simp

/-- One actual balanced hexad supplies Fourier targets for all six unit-residue families. -/
def eisensteinUnitFourierWord : TernaryBalancedWords :=
  ⟨ternaryGolayEquiv ![2,1,1,2,0,2],by decide +kernel⟩

def eisensteinUnitFourierPosition (k : Fin 6) : ternarySupport eisensteinUnitFourierWord.val.val :=
  ⟨(![0,1,2,0,1,0] : Fin 6 → Fin 12) k,by revert k; decide +kernel⟩

def eisensteinUnitFourierPhases (k : Fin 6) : TernaryWord :=
  (![(0 : TernaryWord), ![1,1,0,0,0,0,0,0,0,0,0,0],
    ![2,0,2,0,0,0,0,0,0,0,0,0], ![2,0,2,0,0,0,0,0,0,0,0,0],
    ![0,2,1,0,0,0,0,0,0,0,0,0], ![1,1,0,0,0,0,0,0,0,0,0,0]]) k

def eisensteinUnitFourierParameter (k : Fin 6) : EisensteinBalancedParameters :=
  ⟨eisensteinUnitFourierWord,eisensteinUnitFourierPosition k,
    ⟨fun i => eisensteinUnitFourierPhases k i.val,by
      apply LinearMap.mem_ker.mpr
      change (∑ i : ternarySupport eisensteinUnitFourierWord.val.val,
        eisensteinUnitFourierWord.val.val i.val * eisensteinUnitFourierPhases k i.val)=0
      revert k
      decide +kernel⟩⟩

theorem eisensteinFourier_heavy_balanced :
    eisensteinFourierIsometry • eisensteinHeavyUnitFrame 0 0 =
      eisensteinBalancedParameterFrame (eisensteinUnitFourierParameter 0) := by
  rw [eisensteinHeavyUnitFrame]
  change eisensteinFourierIsometry • eisensteinFrameOfVector
    (eisensteinCodePhaseShell 0 (eisensteinHeavyUnitVector 0)) = _
  rw [unitFourier_phase_zero,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding (eisensteinIntegralAction eisensteinFourierIsometry
    (eisensteinHeavyUnitLattice 0)).val = _
  rw [eisensteinIntegralAction_agrees]
  change eisensteinFourier _ = _
  rw [eisensteinFourier_apply]
  decide +kernel

theorem eisensteinFourier_pair_balanced (b : Bool) :
    eisensteinFourierIsometry • eisensteinPairUnitFrame b eisensteinOrderedBasePair 0 =
      eisensteinBalancedParameterFrame (eisensteinUnitFourierParameter (if b then 2 else 1)) := by
  rw [eisensteinPairUnitFrame,unitFourier_phase_zero,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding (eisensteinIntegralAction eisensteinFourierIsometry
    (eisensteinPairUnitLattice b eisensteinOrderedBasePair)).val = _
  rw [eisensteinIntegralAction_agrees]
  change eisensteinFourier _ = _
  rw [eisensteinFourier_apply]
  revert b
  decide +kernel

theorem eisensteinFourier_unitTriad_balanced (r : Fin 3) :
    eisensteinFourierIsometry • eisensteinTriadUnitFrame r eisensteinBaseTriadEmbedding 0 =
      eisensteinBalancedParameterFrame (eisensteinUnitFourierParameter ⟨r.val+3,by omega⟩) := by
  rw [eisensteinTriadUnitFrame,unitFourier_phase_zero,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding (eisensteinIntegralAction eisensteinFourierIsometry
    (eisensteinTriadUnitLattice r eisensteinBaseTriadEmbedding)).val = _
  rw [eisensteinIntegralAction_agrees]
  change eisensteinFourier _ = _
  rw [eisensteinFourier_apply]
  revert r
  decide +kernel

end Atlas.Conway

import Atlas.Conway.EisensteinNineHexadFrames
import Atlas.Conway.EisensteinUnitFrameCount
import Atlas.Conway.EisensteinBalancedFourier

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

private theorem firstConstantHexad :
    ({0,1,2,3,4,5} : Finset (Fin 12)) ∈ ternaryConstantHexads := by
  apply (mem_ternaryConstantHexads _).mpr
  constructor
  · decide
  · have he : (ternaryGolayEquiv ![1,1,1,1,1,0]).val =
        ternaryTriadWord {0,1,2,3,4,5} := by decide +kernel
    rw [← he]
    exact (ternaryGolayEquiv _).property

/-- A constant-heavy frame is connected directly to the triad family. -/
theorem eisensteinFourier_hexad_triad :
    eisensteinFourierIsometry • eisensteinHexadFrame {0,1,2,3,4,5}
      firstConstantHexad 0 (by decide) =
      eisensteinTriadFrame {1,2,3} (by decide) 0 := by
  rw [eisensteinHexadFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding (eisensteinIntegralAction eisensteinFourierIsometry
    (eisensteinHexadLatticeVector {0,1,2,3,4,5} firstConstantHexad 0)).val = _
  rw [eisensteinIntegralAction_agrees]
  change eisensteinFourier _ = _
  rw [eisensteinFourier_apply]
  decide +kernel

private theorem crossingConstantHexad :
    ({0,1,5,6,7,9} : Finset (Fin 12)) ∈ ternaryConstantHexads := by
  apply (mem_ternaryConstantHexads _).mpr
  constructor
  · decide
  · have he : (ternaryGolayEquiv ![1,1,0,0,0,0]).val =
        ternaryTriadWord {0,1,5,6,7,9} := by decide +kernel
    rw [← he]
    exact (ternaryGolayEquiv _).property

def eisensteinCrossingNineVector (b : ZMod 3) (hb : b≠0) : EisensteinShell 6 :=
  eisensteinNineHexadShellVector {0,1,5,6,7,9} crossingConstantHexad 0 2
    (by decide) (by decide) b hb

/-- Each of the two constant-hexad signs has a Fourier image in the already
exhausted nonzero-residue part of the actual frame space. -/
theorem eisensteinFourier_constantNine_mem_unit (b : ZMod 3) (hb : b≠0) :
    eisensteinFourierIsometry • eisensteinFrameOfVector (eisensteinCrossingNineVector b hb) ∈
      eisensteinUnitResidueFrames := by
  rw [eisensteinFrameAction_vector]
  apply eisensteinNonzeroResidue_mem
  have hc : (eisensteinIntegralAction eisensteinFourierIsometry
      (eisensteinCrossingNineVector b hb).val).val 0 = -2 := by
    apply eisensteinToRational_injective
    change (eisensteinCoordinateEmbedding (eisensteinIntegralAction eisensteinFourierIsometry
      (eisensteinCrossingNineVector b hb).val).val) 0 = eisensteinToRational (-2)
    rw [eisensteinIntegralAction_agrees]
    change eisensteinFourier _ 0 = _
    rw [eisensteinFourier_apply]
    revert hb b
    decide +kernel
  change eisensteinResidue ((eisensteinIntegralAction eisensteinFourierIsometry
    (eisensteinCrossingNineVector b hb).val).val 0) ≠ 0
  rw [hc]
  decide +kernel

end Atlas.Conway

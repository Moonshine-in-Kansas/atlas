import Atlas.Conway.EisensteinBalancedOrbit

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

def eisensteinFourierBalancedWord : TernaryBalancedWords :=
  ⟨ternaryGolayEquiv ![2,2,2,0,0,0],by decide +kernel⟩

def eisensteinFourierBalancedPosition : ternarySupport eisensteinFourierBalancedWord.val.val :=
  ⟨0,by decide +kernel⟩

def eisensteinFourierBalancedPhase : EisensteinBalancedPhase eisensteinFourierBalancedWord :=
  ⟨fun i => (![0,2,1,0,0,0,0,2,0,1,0,0] : TernaryWord) i.val,by
    apply LinearMap.mem_ker.mpr
    change (∑ i : ternarySupport eisensteinFourierBalancedWord.val.val,
      eisensteinFourierBalancedWord.val.val i.val *
        (![0,2,1,0,0,0,0,2,0,1,0,0] : TernaryWord) i.val)=0
    decide +kernel⟩

def eisensteinFourierBalancedParameter : EisensteinBalancedParameters :=
  ⟨eisensteinFourierBalancedWord,eisensteinFourierBalancedPosition,eisensteinFourierBalancedPhase⟩

/-- The corrected Fourier operator joins the triad suborbit to the balanced-heavy suborbit. -/
theorem eisensteinFourier_triad_balanced :
    eisensteinFourierIsometry • eisensteinTriadFrame {0,1,7} (by decide) 0 =
      eisensteinBalancedParameterFrame eisensteinFourierBalancedParameter := by
  rw [eisensteinTriadFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding
    (eisensteinIntegralAction eisensteinFourierIsometry
      (eisensteinTriadLatticeVector {0,1,7} (by decide) 0)).val = _
  rw [eisensteinIntegralAction_agrees]
  change eisensteinFourier _ = _
  rw [eisensteinFourier_apply]
  decide +kernel

theorem eisensteinFourier_triad_mem_balanced :
    eisensteinFourierIsometry • eisensteinTriadFrame {0,1,7} (by decide) 0 ∈
      eisensteinBalancedFamily := by
  rw [eisensteinFourier_triad_balanced]
  exact eisensteinBalancedParameterFrame_mem _

end Atlas.Conway

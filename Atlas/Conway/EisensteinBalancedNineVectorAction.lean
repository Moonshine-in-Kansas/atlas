import Atlas.Conway.EisensteinBalancedNineNegation
import Atlas.Lattices.EisensteinBalancedNineVectorCount

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

def eisensteinBalancedNinePhaseParameter (t : ternaryGolay) (p : EisensteinBalancedNineParameters) :
    EisensteinBalancedNineParameters :=
  ⟨p.1,p.2.1,p.2.2.1,⟨p.2.2.2.1.val+(fun i => t.val i.val),by
    rw [map_add,p.2.2.2.1.prop]
    have hz := ternaryHexadRestriction_le (ternaryBalancedSixWord p.1) ⟨t,rfl⟩
    rw [LinearMap.mem_ker] at hz
    change ternaryHexadFunctional (ternaryBalancedSixWord p.1) (fun i => t.val i.val)=0 at hz
    rw [hz,add_zero]⟩,p.2.2.2.2+t.val p.2.1.val⟩

theorem eisensteinBalancedNinePhaseParameter_action (t : ternaryGolay)
    (p : EisensteinBalancedNineParameters) :
    eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t))
      (eisensteinBalancedNineParameterLatticeVector p)=
        eisensteinBalancedNineParameterLatticeVector (eisensteinBalancedNinePhaseParameter t p) := by
  apply Subtype.ext
  rw [eisensteinIntegralAction_phase]
  apply eisensteinBalancedNineVector_phase
  · intro i
    change t.val i.val=p.2.2.2.1.val i+t.val i.val-p.2.2.2.1.val i
    ring
  · change t.val p.2.1.val=p.2.2.2.2+t.val p.2.1.val-p.2.2.2.2
    ring

def eisensteinBalancedNineCoordinateParameter (g : TernaryPureAutomorphism)
    (p : EisensteinBalancedNineParameters) : EisensteinBalancedNineParameters :=
  ⟨ternaryBalancedPermutation g p.1,⟨g.val p.2.1.val,by
    change g.val p.2.1.val ∉ ternarySupport (fun i => p.1.val.val (g.val.symm i))
    simpa [ternarySupport] using p.2.1.prop⟩,p.2.2.1,
    eisensteinBalancedNinePermutedPhase p.1 (ternaryBalancedPermutation g p.1) g (fun _ => rfl)
      p.2.2.1 p.2.2.2.1,p.2.2.2.2⟩

theorem eisensteinBalancedNineCoordinateParameter_action (g : TernaryPureAutomorphism)
    (p : EisensteinBalancedNineParameters) :
    eisensteinIntegralAction (eisensteinCoordinateIsometries g)
      (eisensteinBalancedNineParameterLatticeVector p)=
        eisensteinBalancedNineParameterLatticeVector (eisensteinBalancedNineCoordinateParameter g p) :=
  eisensteinBalancedNine_coordinate _ _ g (fun _ => rfl) _ _ rfl _ _ _

theorem eisensteinBalancedNineParameter_action (g : eisensteinCoordinateFrameStabilizer)
    (p : EisensteinBalancedNineParameters) :
    ∃ q : EisensteinBalancedNineParameters,
      eisensteinIntegralAction g.val (eisensteinBalancedNineParameterLatticeVector p)=
        eisensteinBalancedNineParameterLatticeVector q := by
  obtain ⟨⟨b,t,σ⟩,rfl⟩ := eisensteinFrameFromParameters_surjective g
  let q := eisensteinBalancedNinePhaseParameter t (eisensteinBalancedNineCoordinateParameter σ p)
  have hm : eisensteinIntegralAction (eisensteinMonomialParameterIsometry (false,t,σ))
      (eisensteinBalancedNineParameterLatticeVector p)=eisensteinBalancedNineParameterLatticeVector q := by
    have he : eisensteinMonomialParameterIsometry (false,t,σ)=
        eisensteinPhaseIsometries (Multiplicative.ofAdd t)*eisensteinCoordinateIsometries σ := by
      simp [eisensteinMonomialParameterIsometry]
    rw [he,eisensteinIntegralAction_mul,eisensteinBalancedNineCoordinateParameter_action,
      eisensteinBalancedNinePhaseParameter_action]
  cases b
  · exact ⟨q,hm⟩
  · refine ⟨eisensteinBalancedNineNegParameter q,?_⟩
    change eisensteinIntegralAction (eisensteinMonomialParameterIsometry (true,t,σ)) _ = _
    have he : eisensteinMonomialParameterIsometry (true,t,σ)=
        eisensteinSignIsometry*eisensteinMonomialParameterIsometry (false,t,σ) := by
      simp [eisensteinMonomialParameterIsometry,mul_assoc]
    rw [he,eisensteinIntegralAction_mul,hm,eisensteinSignIntegral,
      eisensteinBalancedNineNegParameter_vector]

theorem eisensteinBalancedNineVectors_invariant (g : eisensteinCoordinateFrameStabilizer)
    (x : EisensteinShell 6) (hx : x ∈ eisensteinBalancedNineVectors) :
    eisensteinShellAction g.val 6 x ∈ eisensteinBalancedNineVectors := by
  classical
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq⟩ := eisensteinBalancedNineParameter_action g p
  refine Finset.mem_image.mpr ⟨q,Finset.mem_univ _,?_⟩
  apply Subtype.ext
  exact hq.symm

end Atlas.Conway

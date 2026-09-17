import Atlas.Conway.EisensteinBalancedClassProfile

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

def eisensteinClassFiberAction (g : eisensteinHermitianGroup) (r : ℤ) (c : EisensteinClasses) :
    EisensteinClassFiber r c ≃ EisensteinClassFiber r (eisensteinClassAction g c) :=
  (eisensteinShellAction g r).subtypeEquiv (fun x => by
    change eisensteinClass x.val=c ↔
      eisensteinClass (eisensteinIntegralAction g x.val)=eisensteinClassAction g c
    rw [← eisensteinClassAction_mk]
    exact (eisensteinClassAction g).injective.eq_iff.symm)

def eisensteinBalancedProfileFiberEquiv : EisensteinBalancedClassParameter ≃
    EisensteinClassFiber 6 (eisensteinClassAction eisensteinFourierIsometry
      (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} (by decide) 0))) :=
  (Equiv.ofBijective eisensteinBalancedSourceFiber eisensteinBalancedSourceFiber_bijective).trans
    (eisensteinClassFiberAction eisensteinFourierIsometry 6 _)

theorem eisensteinBalancedProfileFiberEquiv_coordinates (p : EisensteinBalancedClassParameter) :
    (eisensteinBalancedProfileFiberEquiv p).val.val.val=eisensteinBalancedProfileVector p := by
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding
    (eisensteinIntegralAction eisensteinFourierIsometry (eisensteinBalancedSourceVector p)).val = _
  rw [eisensteinIntegralAction_agrees]
  exact eisensteinBalancedProfileVector_fourier p

/-- Every vector in the actual oriented Fourier-image class is one of the 36
structurally parametrized vectors, whose profiles are nine heavy and27 weight-nine. -/
theorem eisensteinBalancedProfile_exhaustion
    (x : EisensteinClassFiber 6 (eisensteinClassAction eisensteinFourierIsometry
      (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} (by decide) 0)))) :
    ∃ p : EisensteinBalancedClassParameter,x.val.val.val=eisensteinBalancedProfileVector p := by
  obtain ⟨p,rfl⟩ := eisensteinBalancedProfileFiberEquiv.surjective x
  exact ⟨p,eisensteinBalancedProfileFiberEquiv_coordinates p⟩

end Atlas.Conway

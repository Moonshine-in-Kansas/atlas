import Atlas.Conway.EisensteinBalancedNineProfileData
import Atlas.Conway.EisensteinBalancedProfileExclusions

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinNineProfile_coordinates (p : EisensteinBalancedClassParameter) :
    (eisensteinIntegralAction eisensteinNineBridgeIsometry (eisensteinBalancedSourceVector p)).val =
      eisensteinNineProfileVector p := by
  apply eisensteinCoordinateEmbedding_injective
  rw [eisensteinIntegralAction_agrees]
  change eisensteinFourier
    ((eisensteinMonomialParameterIsometry
      (false,eisensteinNineBridgePhase,eisensteinNineBridgeCodePermutation)).val
      (eisensteinFourier (eisensteinCoordinateEmbedding (eisensteinBalancedSourceVector p).val))) = _
  rw [eisensteinBalancedProfileVector_fourier,eisensteinFourier_apply]
  rcases p with ⟨b,a,d⟩
  fin_cases b <;> fin_cases a <;> fin_cases d <;> decide +kernel

def eisensteinNineProfileFiberEquiv : EisensteinBalancedClassParameter ≃
    EisensteinClassFiber 6 (eisensteinClassAction eisensteinNineBridgeIsometry
      (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0))) :=
  (Equiv.ofBijective eisensteinBalancedSourceFiber eisensteinBalancedSourceFiber_bijective).trans
    (eisensteinClassFiberAction eisensteinNineBridgeIsometry 6 _)

theorem eisensteinNineProfile_exhaustion
    (x : EisensteinClassFiber 6 (eisensteinClassAction eisensteinNineBridgeIsometry
      (eisensteinClass (eisensteinTriadLatticeVector {0,1,7} eisensteinBalancedSourceBase_card 0)))) :
    ∃ p : EisensteinBalancedClassParameter,x.val.val.val=eisensteinNineProfileVector p := by
  obtain ⟨p,rfl⟩ := eisensteinNineProfileFiberEquiv.surjective x
  exact ⟨p,eisensteinNineProfile_coordinates p⟩

def eisensteinNineProfileCount (p : EisensteinBalancedClassParameter) (n : ℤ) : ℕ :=
  (Finset.univ.filter (fun i => (eisensteinNineProfileVector p i).norm=n)).card

theorem eisensteinNineProfile_counts :
    (Finset.univ.filter (fun p : EisensteinBalancedClassParameter =>
      eisensteinNineProfileCount p 9=1)).card=18 ∧
    (Finset.univ.filter (fun p : EisensteinBalancedClassParameter =>
      eisensteinNineProfileCount p 3=9)).card=18 := by decide +kernel

theorem eisensteinNineProfile_patterns : ∀ p : EisensteinBalancedClassParameter,
    (eisensteinNineProfileCount p 0=5 ∧ eisensteinNineProfileCount p 3=6 ∧
      eisensteinNineProfileCount p 9=1) ∨
    (eisensteinNineProfileCount p 0=3 ∧ eisensteinNineProfileCount p 3=9) := by decide +kernel

end Atlas.Conway

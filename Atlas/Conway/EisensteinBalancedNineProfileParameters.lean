import Atlas.Conway.EisensteinBalancedNineProfile
import Atlas.Lattices.EisensteinBalancedNineVectorCount

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

def eisensteinNineProfileChoice (p : EisensteinBalancedClassParameter) : EisensteinBalancedClassParameter :=
  if eisensteinNineProfileCount p 9=1 then p else (0,0,0)

def eisensteinNineProfileNormalized (p : EisensteinBalancedClassParameter) (i : Fin 12) : Eisenstein :=
  let z := eisensteinNineProfileVector (eisensteinNineProfileChoice p) i
  ⟨(-z.re+2*z.im)/3,(-2*z.re+z.im)/3⟩

def eisensteinNineProfileCodeWord (p : EisensteinBalancedClassParameter) : TernaryWord :=
  eisensteinWordResidue (eisensteinNineProfileNormalized p)

def eisensteinNineProfileCode (p : EisensteinBalancedClassParameter) : TernaryBalancedWords :=
  ⟨ternaryGolayEquiv (ternaryDecoder (eisensteinNineProfileCodeWord p)),by revert p; decide +kernel⟩

def eisensteinNineProfileHeavy (p : EisensteinBalancedClassParameter) : Fin 12 :=
  ((List.finRange 12).find? (fun i => decide
    ((eisensteinNineProfileVector (eisensteinNineProfileChoice p) i).norm=9))).getD 0

def eisensteinNineProfileHeavyScalar (p : EisensteinBalancedClassParameter) : Eisenstein :=
  let z := eisensteinNineProfileVector (eisensteinNineProfileChoice p) (eisensteinNineProfileHeavy p)
  ⟨-z.re/3,-z.im/3⟩

def eisensteinNineProfileHeavySign (p : EisensteinBalancedClassParameter) : Bool :=
  decide (eisensteinResidue (eisensteinNineProfileHeavyScalar p)=2)

def eisensteinUnitPhaseIndex (z : Eisenstein) : ZMod 3 :=
  if z=1 then 0 else if z=eisensteinOmega then 1 else 2

def eisensteinNineProfilePhaseWord (p : EisensteinBalancedClassParameter) : TernaryWord :=
  fun i => eisensteinUnitPhaseIndex
    ((ternarySignedLift (eisensteinNineProfileCodeWord p i) : Eisenstein)*eisensteinNineProfileNormalized p i)

def eisensteinNineProfileRawPhase (p : EisensteinBalancedClassParameter) :
    EisensteinBalancedNinePhase (eisensteinNineProfileCode p) (eisensteinNineProfileHeavySign p) :=
  ⟨fun i => eisensteinNineProfilePhaseWord p i.val,by
    change (∑ i : ternarySupport (eisensteinNineProfileCode p).val.val,
      (eisensteinNineProfileCode p).val.val i.val*eisensteinNineProfilePhaseWord p i.val)=_
    revert p
    decide +kernel⟩

def eisensteinNineProfileRawParameter (p : EisensteinBalancedClassParameter) : EisensteinBalancedNineParameters :=
  ⟨eisensteinNineProfileCode p,⟨eisensteinNineProfileHeavy p,by revert p; decide +kernel⟩,
    eisensteinNineProfileHeavySign p,eisensteinNineProfileRawPhase p,
    eisensteinUnitPhaseIndex (eisensteinBalancedNineSign (eisensteinNineProfileHeavySign p)*
      eisensteinNineProfileHeavyScalar p)⟩

/-- The local norm-nine images are reconstructed as actual raw lattice parameters. -/
theorem eisensteinNineProfileRaw_correct : ∀ p : EisensteinBalancedClassParameter,
    eisensteinNineProfileCount p 9=1 →
      eisensteinBalancedNineParameterVector (eisensteinNineProfileRawParameter p)=eisensteinNineProfileVector p := by
  decide +kernel

end Atlas.Conway

import Atlas.Conway.EisensteinFrameGroup
import Atlas.Mathieu.TernaryPhaseSemidirect
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- Quotient of the actual code by its constant words. -/
def eisensteinCodePhaseQuotient : Multiplicative ternaryGolay →*
    Multiplicative TernaryPhaseModule where
  toFun t := Multiplicative.ofAdd (ternaryConstants.mkQ t.toAdd)
  map_one' := congrArg Multiplicative.ofAdd (map_zero ternaryConstants.mkQ)
  map_mul' t u := congrArg Multiplicative.ofAdd (map_add ternaryConstants.mkQ t.toAdd u.toAdd)

theorem eisensteinCodePhaseQuotient_equivariant (g : TernaryPureAutomorphism) :
    eisensteinCodePhaseQuotient.comp (eisensteinCodeActionHom g).toMonoidHom =
      (ternaryPhaseMultiplicativeAction g).toMonoidHom.comp eisensteinCodePhaseQuotient := by
  apply MonoidHom.ext
  intro t
  rfl

def eisensteinSemidirectPhaseQuotient : EisensteinCodeSemidirect →* TernaryLocalPhaseGroup :=
  SemidirectProduct.map eisensteinCodePhaseQuotient (MonoidHom.id _) eisensteinCodePhaseQuotient_equivariant

def eisensteinAbstractPhaseQuotient : EisensteinFrameAbstractGroup →* TernaryLocalPhaseGroup :=
  eisensteinSemidirectPhaseQuotient.comp (MonoidHom.snd _ _)

/-- The actual full coordinate-frame stabilizer maps to the five-dimensional
phase group with its actual M11 action. -/
def eisensteinFramePhaseQuotient : eisensteinCoordinateFrameStabilizer →* TernaryLocalPhaseGroup :=
  eisensteinAbstractPhaseQuotient.comp eisensteinFullFrameGroupEquiv.symm.toMonoidHom

theorem eisensteinAbstractPhaseQuotient_surjective : Function.Surjective eisensteinAbstractPhaseQuotient := by
  intro x
  obtain ⟨t,ht⟩ := Submodule.Quotient.mk_surjective ternaryConstants x.left.toAdd
  refine ⟨(1,⟨Multiplicative.ofAdd t,x.right⟩),?_⟩
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd ht
  · rfl

theorem eisensteinFramePhaseQuotient_surjective : Function.Surjective eisensteinFramePhaseQuotient :=
  eisensteinAbstractPhaseQuotient_surjective.comp eisensteinFullFrameGroupEquiv.symm.surjective

theorem eisensteinAbstractPhaseQuotient_kernel (x : EisensteinFrameAbstractGroup) :
    x ∈ eisensteinAbstractPhaseQuotient.ker ↔ x.2.left.toAdd ∈ ternaryConstants ∧ x.2.right = 1 := by
  change (⟨eisensteinCodePhaseQuotient x.2.left,x.2.right⟩ : TernaryLocalPhaseGroup) = 1 ↔ _
  constructor
  · intro h
    refine ⟨?_,congrArg SemidirectProduct.right h⟩
    exact (Submodule.Quotient.mk_eq_zero ternaryConstants).mp
      (congrArg (fun y : TernaryLocalPhaseGroup => y.left.toAdd) h)
  · rintro ⟨hl,hr⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd ((Submodule.Quotient.mk_eq_zero ternaryConstants).mpr hl)
    · exact hr

/-- First isomorphism theorem for the actual frame stabilizer. Identification
of this kernel with all six scalar units is provided separately. -/
def eisensteinFramePhaseQuotientEquiv :
    eisensteinCoordinateFrameStabilizer ⧸ eisensteinFramePhaseQuotient.ker ≃* TernaryLocalPhaseGroup :=
  QuotientGroup.quotientKerEquivOfSurjective eisensteinFramePhaseQuotient eisensteinFramePhaseQuotient_surjective

theorem eisensteinFramePhaseQuotient_order :
    Nat.card (eisensteinCoordinateFrameStabilizer ⧸ eisensteinFramePhaseQuotient.ker) = 1924560 :=
  (Nat.card_congr eisensteinFramePhaseQuotientEquiv.toEquiv).trans ternaryLocalPhaseGroup_order

end Atlas.Conway

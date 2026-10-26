import Atlas.Tits.Simplicity
import Atlas.Tits.RetainedAction
import Atlas.Tits.CharacterConsequences
import Atlas.Tits.PointRowKernelOrder

/-! Public package for the derived Tits group in the inherited Conway–Wales
construction. All endpoints refer to the literal commutator subgroup of the
actual Rudvalis cross stabilizer. No separate Ree-model comparison is asserted. -/
namespace Atlas.Tits

theorem finite : Finite Model := inferInstance

theorem order : Nat.card Model = 2^11 * 3^3 * 5^2 * 13 := by
  rw [card]
  decide

theorem model_is_derived : derivedSubgroup = commutator Ambient := rfl

/-- The same concrete model has the proved order, simplicity, noncommutativity
and faithful inclusion in the existing Rudvalis construction. -/
theorem construction :
    Finite Model ∧ Nat.card Model = 17971200 ∧ IsSimpleGroup Model ∧
      (∃ a b : Model, a*b ≠ b*a) ∧ Function.Injective embeddingIntoRudvalis ∧
      derivedSubgroup = transfer.ker ∧ derivedSubgroup.index = 2 :=
  ⟨finite,card,isSimpleGroup,noncommutative,embeddingIntoRudvalis_injective,
    derived_eq_transferKernel,index_derived⟩

end Atlas.Tits

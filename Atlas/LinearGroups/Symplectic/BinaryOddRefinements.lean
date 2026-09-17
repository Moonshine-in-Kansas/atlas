import Atlas.LinearGroups.Symplectic.BinaryRefinements
import Mathlib.GroupTheory.GroupAction.Hom

noncomputable section
namespace Atlas.Symplectic.BinaryException

def zeroCount (Q : Refinement) : ℕ := Nat.card {x : V // Q.val x=0}
abbrev OddRefinement := {Q : Refinement // zeroCount Q=6}
abbrev OddParameter := {a : V // baseQuadratic a=1}

/-- The count is on sixteen vectors for each of sixteen explicitly parametrized forms. -/
theorem zeroCount_refinement_iff (a : V) : zeroCount (refinementOf a)=6 ↔ baseQuadratic a=1 := by
  change Nat.card {x : V // (refinementOf a).val x=0}=6 ↔ _
  rw [Nat.card_eq_fintype_card]
  exact (by decide +kernel : ∀ a : V,
    Fintype.card {x : V // (refinementOf a).val x=0}=6 ↔ baseQuadratic a=1) a

def oddRefinementEquiv : OddParameter ≃ OddRefinement :=
  Equiv.subtypeEquiv refinementEquiv (fun a => (zeroCount_refinement_iff a).symm)

theorem card_oddRefinement : Nat.card OddRefinement=6 := by
  rw [← Nat.card_congr oddRefinementEquiv,Nat.card_eq_fintype_card]
  decide +kernel

@[simp] theorem refinementAction_apply (g : Sp 2 K) (Q : Refinement) (x : V) :
    (g • Q).val x=Q.val (g⁻¹ • x) := rfl

theorem zeroCount_invariant (g : Sp 2 K) (Q : Refinement) : zeroCount (g • Q)=zeroCount Q := by
  exact formRefinement_zeroCount_invariant g Q

/-- The actual symplectic isometries permute the six odd quadratic refinements. -/
instance oddRefinementAction : MulAction (Sp 2 K) OddRefinement where
  smul g Q := ⟨g • Q.val,by rw [zeroCount_invariant,Q.prop]⟩
  one_smul Q := by apply Subtype.ext; exact one_smul _ _
  mul_smul g h Q := by apply Subtype.ext; exact mul_smul _ _ _

@[simp] theorem oddRefinementAction_apply (g : Sp 2 K) (Q : OddRefinement) (x : V) :
    (g • Q).val.val x=Q.val.val (g⁻¹ • x) := rfl

end Atlas.Symplectic.BinaryException

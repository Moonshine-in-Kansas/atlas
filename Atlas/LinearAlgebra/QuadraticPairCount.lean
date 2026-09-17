import Atlas.LinearAlgebra.QuadraticSplit
import Mathlib.FieldTheory.Finiteness

/-! # Counting singular partners by their actual perpendicular complement -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

/-- A singular normalized partner is specified uniquely by its perpendicular component. -/
def partnerEquivComplement :
    {x : V // Q x = 0 ∧ Q.polarBilin e x = 1} ≃ complement Q e f := by
  let C := complement Q e f
  let P : (F × F) × C → Prop := fun t => t.1.1*t.1.2+Q t.2.val=0 ∧ t.1.2=1
  let h : ∀ x, (Q x=0 ∧ Q.polarBilin e x=1) ↔ P (split Q e f he hf hef x) := by
    intro x
    dsimp only [P]
    rw [← form_split Q e f he hf hef x]
    change (Q x=0 ∧ Q.polarBilin e x=1) ↔ (Q x=0 ∧ Q.polarBilin x e=1)
    rw [polar_swap Q e x]
  refine (Equiv.subtypeEquiv (split Q e f he hf hef).toEquiv h).trans ?_
  refine { toFun := fun t => t.val.2
           invFun := fun w => ⟨((-Q w.val,1),w), ?_⟩
           left_inv := ?_
           right_inv := fun _ => rfl }
  · change -Q w.val * 1 + Q w.val = 0 ∧ (1 : F)=1
    simp
  · rintro ⟨⟨⟨a,b⟩,w⟩,hq,hb⟩
    change b=1 at hb
    subst b
    change a*1+Q w.val=0 at hq
    have ha : a = -Q w.val := eq_neg_of_add_eq_zero_left (by simpa using hq)
    apply Subtype.ext
    simp only [ha]

include f he hf hef in
/-- Partner count, proved from a bijection rather than an assumed group order. -/
theorem card_partners [Finite F] [FiniteDimensional F V] :
    Nat.card {x : V // Q x = 0 ∧ Q.polarBilin e x = 1} =
      Nat.card F ^ (Module.finrank F V - 2) := by
  have hd := finrank_complement Q e f he hf hef
  have hr : Module.finrank F (complement Q e f) = Module.finrank F V - 2 := by omega
  rw [Nat.card_congr (partnerEquivComplement Q e f he hf hef),
    Module.natCard_eq_pow_finrank (K := F),hr]

end Atlas.Quadratic

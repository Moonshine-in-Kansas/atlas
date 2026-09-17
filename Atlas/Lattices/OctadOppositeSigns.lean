import Atlas.Lattices.SupportSigns
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def OppositeParitySigns (α : Type*) [Fintype α] (a b : α) :=
  {s : α → Bit // (∑ i, s i) = 0 ∧ s a ≠ s b}

instance (α : Type*) [Fintype α] (a b : α) : Finite (OppositeParitySigns α a b) :=
  inferInstanceAs (Finite {s : α → Bit // (∑ i, s i) = 0 ∧ s a ≠ s b})

def oppositeParitySignsCongr {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (a b : α) : OppositeParitySigns α a b ≃ OppositeParitySigns β (e a) (e b) where
  toFun s := ⟨fun i => s.val (e.symm i),by
    constructor
    · rw [Equiv.sum_comp]; exact s.prop.1
    · simpa only [Equiv.symm_apply_apply] using s.prop.2⟩
  invFun s := ⟨fun i => s.val (e i),by
    constructor
    · rw [Equiv.sum_comp]; exact s.prop.1
    · exact s.prop.2⟩
  left_inv s := by apply Subtype.ext; funext i; simp
  right_inv s := by apply Subtype.ext; funext i; simp

set_option maxRecDepth 100000 in
theorem oppositeParitySigns_fin8_card :
    Nat.card (OppositeParitySigns (Fin 8) 0 1) = 64 := by
  change Nat.card {s : Fin 8 → Bit // (∑ i, s i) = 0 ∧ s 0 ≠ s 1} = 64
  rw [Nat.card_eq_fintype_card]
  decide

theorem oppositeParitySigns_eight_card (α : Type*) [Fintype α] (hα : Fintype.card α = 8)
    (a b : α) (hab : a ≠ b) : Nat.card (OppositeParitySigns α a b) = 64 := by
  let e := Fintype.equivFinOfCardEq hα
  obtain ⟨σ,hσa,hσb⟩ := (MulAction.is_two_pretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive (Fin 8) 2)) (e.injective.ne hab) (by decide : (0 : Fin 8) ≠ 1)
  let f : α ≃ Fin 8 := e.trans σ
  have ha : f a = 0 := hσa
  have hb : f b = 1 := hσb
  rw [Nat.card_congr (oppositeParitySignsCongr f a b),ha,hb,oppositeParitySigns_fin8_card]

end Atlas.Lattices

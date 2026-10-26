import Mathlib.Logic.Equiv.Sum
import Mathlib.SetTheory.Cardinal.Finite

namespace Atlas

theorem card_predicate_split {α : Type*} [Finite α] (p q : α → Prop) :
    Nat.card {x // p x} = Nat.card {x // p x ∧ q x} + Nat.card {x // p x ∧ ¬q x} := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl (fun x : {x // p x} => q x.val))
  rw [Nat.card_sum,
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p q),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p (fun x => ¬q x))] at h
  exact h.symm

end Atlas

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace Atlas.GroupTheory

/-- A faithful transitive commutative group has the same cardinality as its action set. -/
theorem card_eq_degree_of_commutative {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] (a : X)
    (comm : ∀ g h : G, g * h = h * g) : Nat.card G = Nat.card X := by
  have hi : Function.Injective (fun g : G => g • a) := by
    intro g h he
    change g • a = h • a at he
    apply eq_of_smul_eq_smul (α := X)
    intro x
    obtain ⟨k,rfl⟩ := MulAction.exists_smul_eq G a x
    rw [← mul_smul, comm g k, mul_smul, he, ← mul_smul, comm k h, mul_smul]
  exact Nat.card_congr (Equiv.ofBijective _ ⟨hi,fun x => MulAction.exists_smul_eq G a x⟩)

theorem noncommuting_of_card_ne_degree {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] (a : X)
    (hne : Nat.card G ≠ Nat.card X) : ∃ g h : G, g * h ≠ h * g := by
  classical
  by_contra h
  push_neg at h
  exact hne (card_eq_degree_of_commutative a h)

end Atlas.GroupTheory

import Mathlib.GroupTheory.Perm.Cycle.Type

namespace Atlas.GroupTheory

/-- The sign of an involution is determined by its fixed-point count. -/
theorem action_sign_involution {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] [DecidableEq X] (g : G) (hg : g^2=1) :
    Equiv.Perm.sign (MulAction.toPermHom G X g) =
      (-1)^((Nat.card X-Nat.card {x:X // g • x=x})/2) := by
  have hp : (MulAction.toPermHom G X g)^2=1 := by rw [← map_pow,hg,map_one]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hp]
  congr 2
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  rfl

end Atlas.GroupTheory

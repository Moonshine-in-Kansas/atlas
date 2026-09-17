import Mathlib.GroupTheory.Perm.Sign

namespace Atlas.GroupTheory

theorem even_fixed_outside_pair {X : Type*} [Fintype X] [DecidableEq X]
    (a b : X) (σ : Equiv.Perm X) (heven : Equiv.Perm.sign σ = 1)
    (hfix : ∀ x, x ≠ a → x ≠ b → σ x = x) : σ = 1 := by
  have hs : σ.support ⊆ {a,b} := by
    intro x hx
    by_contra hn
    have hxa : x ≠ a := fun h => hn (by simp [h])
    have hxb : x ≠ b := fun h => hn (by simp [h])
    exact Equiv.Perm.mem_support.mp hx (hfix x hxa hxb)
  have hcard : σ.support.card ≤ 2 := (Finset.card_le_card hs).trans (by simpa using Finset.card_insert_le a ({b} : Finset X))
  by_contra h
  have hlow := Equiv.Perm.two_le_card_support_of_ne_one h
  have hswap := Equiv.Perm.card_support_eq_two.mp (Nat.le_antisymm hcard hlow)
  have hn := hswap.sign_eq
  rw [heven] at hn
  exact (by decide : (1 : ℤˣ) ≠ -1) hn

end Atlas.GroupTheory

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Atlas.Algebra

/-- A p-subgroup contains no element of a different prime order. -/
theorem prime_order_not_mem_pgroup {G : Type*} [Group G] {p q : ℕ}
    [Fact p.Prime] (N : Subgroup G) (hN : IsPGroup p N) (hq : q.Prime)
    (hpq : p ≠ q) (x : G) (hx : orderOf x=q) : x ∉ N := by
  intro hm
  have hn : (⟨x,hm⟩ : N) ≠ 1 := by
    intro he
    have he' : x=1 := congrArg Subtype.val he
    rw [he',orderOf_one] at hx
    exact hq.ne_one hx.symm
  have hd := hN.dvd_orderOf hn
  rw [Subgroup.orderOf_mk,hx] at hd
  rcases hq.eq_one_or_self_of_dvd p hd with h | h
  · exact (Fact.out : p.Prime).ne_one h
  · exact hpq h

/-- A homomorphism with p-group kernel preserves every different prime order. -/
theorem orderOf_map_prime_of_pgroup_kernel {G H : Type*} [Group G] [Group H]
    {p q : ℕ} [Fact p.Prime] (f : G →* H) (hk : IsPGroup p f.ker)
    (hq : q.Prime) (hpq : p ≠ q) (x : G) (hx : orderOf x=q) :
    orderOf (f x)=q := by
  have hd := orderOf_map_dvd f x
  rw [hx] at hd
  rcases hq.eq_one_or_self_of_dvd _ hd with h | h
  · have hm : x ∈ f.ker := orderOf_eq_one_iff.mp h
    exact (prime_order_not_mem_pgroup f.ker hk hq hpq x hx hm).elim
  · exact h

end Atlas.Algebra

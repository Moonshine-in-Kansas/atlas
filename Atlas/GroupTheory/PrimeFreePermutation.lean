import Mathlib.GroupTheory.Perm.Cycle.Type

namespace Atlas.GroupTheory

/-- A permutation of prime exponent without fixed points partitions a finite set
into cycles of that prime length. -/
theorem prime_dvd_card_of_fixedPointFree {X : Type*} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) (p : ℕ) (hp : p.Prime) (hg : g ^ p = 1)
    (hf : ∀ x, g x ≠ x) : p ∣ Fintype.card X := by
  letI : Fact p.Prime := ⟨hp⟩
  have hs : g.support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support,hf x]
  have he := Equiv.Perm.cycleType_of_pow_prime_eq_one hg
  have hc := g.sum_cycleType
  rw [he,Multiset.sum_replicate,hs,Finset.card_univ] at hc
  exact ⟨g.cycleType.card,by simpa [mul_comm] using hc.symm⟩

end Atlas.GroupTheory

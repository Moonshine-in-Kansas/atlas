import Atlas.OrderArithmetic.RankOneMersenne
import Atlas.OrderArithmetic.RankOneEvenDominance

namespace Atlas.OrderArithmetic

/-- Every failure of characteristic dominance in the rank-one linear formula
belongs to the stated Mersenne, Fermat, or binary cubic exception. -/
theorem linear_two_cross_large_exceptions {q p f l : ℕ}
    (hx : Admissible (.linear 2 q)) (hp : p.Prime) (hf : 1 ≤ f)
    (hq : q = p ^ f) (hl : l.Prime) (hlp : l ≠ p)
    (hlarge : q ≤ l ^ (order (.linear 2 q)).factorization l) :
    (q.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q + 1 = 2 ^ k) ∨
      (p = 2 ∧ (q + 1).Prime) ∨ q = 8 := by
  have hlq : ¬ l ∣ q := by
    intro hd
    rw [hq] at hd
    exact hlp (Nat.prime_eq_prime_of_dvd_pow hl hp hd)
  by_cases hp2 : p = 2
  · subst p
    rcases linear_two_even_cross_large_forces_fermat_or_eight hx hf hq hl hlq
        hlarge with hprime | h8
    · exact Or.inr (Or.inl ⟨rfl, hprime⟩)
    · exact Or.inr (Or.inr h8)
  · have ho : Odd q := by rw [hq]; exact (hp.odd_of_ne_two hp2).pow
    exact Or.inl (linear_two_odd_cross_large_forces_mersenne_prime hx ho hl hlq hlarge).2

/-- Uniform strict dominance in rank one, with all three explicit exclusions. -/
theorem linear_two_characteristic_dominance {q p f l : ℕ}
    (hx : Admissible (.linear 2 q)) (hp : p.Prime) (hf : 1 ≤ f)
    (hq : q = p ^ f) (hl : l.Prime) (hlp : l ≠ p)
    (hm : ¬ (q.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q + 1 = 2 ^ k))
    (hfermat : ¬ (p = 2 ∧ (q + 1).Prime)) (h8 : q ≠ 8) :
    l ^ (order (.linear 2 q)).factorization l < q := by
  by_contra h
  rcases linear_two_cross_large_exceptions hx hp hf hq hl hlp (by omega) with
    hm' | hf' | h8'
  · exact hm hm'
  · exact hfermat hf'
  · exact h8 h8'

end Atlas.OrderArithmetic

import Atlas.OrderArithmetic.UnitaryBinaryDominance
import Atlas.OrderArithmetic.UnitaryTwoDominance

namespace Atlas.OrderArithmetic

/-- Strict characteristic dominance for all unitary dimensions at least five,
including the binary field and every cross prime. -/
theorem unitary_cross_contribution_lt_of_five_le {d q l : ℕ}
    (hx : Admissible (.unitary d q)) (hd : 5 ≤ d)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.unitary d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  by_cases hq2 : q = 2
  · subst q
    exact unitary_binary_cross_contribution_lt_of_five_le hx hd hl hlq
  have hq : 3 ≤ q := by have := primePower_two_le hx.2.1; omega
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    exact unitary_two_contribution_lt_of_five_le hx hd ho
  · exact unitary_odd_cross_contribution_lt_of_five_le hx hd hq hl hl2 hlq

end Atlas.OrderArithmetic

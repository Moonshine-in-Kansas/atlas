import Atlas.OrderArithmetic.HighRankBoundary
import Atlas.OrderArithmetic.LinearFourDominance
import Atlas.OrderArithmetic.LinearFiveSixDominance
import Atlas.OrderArithmetic.SymplecticSmallDominance

namespace Atlas.OrderArithmetic

/-- Every linear formula of dimension at least three has strict defining-prime
power dominance, uniformly in all admissible fields. -/
theorem linear_cross_contribution_lt_of_three_le {d q l : ℕ}
    (hx : Admissible (.linear d q)) (hd : 3 ≤ d)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  by_cases h7 : 7 ≤ d
  · exact linear_cross_contribution_lt_of_seven_le hx h7 hl hlq
  have hcases : d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
  rcases hcases with rfl | rfl | hd56
  · exact linear_three_cross_contribution_lt hx hl hlq
  · exact linear_four_cross_contribution_lt hx hl hlq
  · exact linear_five_six_cross_contribution_lt hx hd56 hl hlq

/-- Every admissible symplectic numerical order has strict defining-prime
power dominance. -/
theorem symplectic_cross_contribution_lt {r q l : ℕ}
    (hx : Admissible (.C r q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.C r q)).factorization l < q ^ (r ^ 2) := by
  by_cases h4 : 4 ≤ r
  · exact symplectic_cross_contribution_lt_of_four_le hx h4 hl hlq
  have hr := hx.1
  have hh : r = 2 ∨ r = 3 := by omega
  rcases hh with rfl | rfl
  · exact symplectic_rank_two_cross_contribution_lt hx hl hlq
  · exact symplectic_rank_three_cross_contribution_lt hx hl hlq

/-- The B and C integer order formulas agree; the same uniform bound applies. -/
theorem odd_orthogonal_cross_contribution_lt {r q l : ℕ}
    (hx : Admissible (.B r q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.B r q)).factorization l < q ^ (r ^ 2) := by
  rw [order_B_eq_C]
  exact symplectic_cross_contribution_lt hx hl hlq

end Atlas.OrderArithmetic

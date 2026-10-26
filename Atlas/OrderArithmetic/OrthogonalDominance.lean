import Atlas.OrderArithmetic.OrthogonalFourDominance
import Atlas.OrderArithmetic.OrthogonalFiveDominance

namespace Atlas.OrderArithmetic

/-- Uniform strict defining-prime dominance for every admissible split-D formula. -/
theorem split_orthogonal_cross_contribution_lt {r q l : ℕ}
    (hx : Admissible (.Dplus r q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dplus r q)).factorization l < q ^ (r * (r - 1)) := by
  by_cases hr : 6 ≤ r
  · exact split_orthogonal_cross_contribution_lt_of_six_le hx hr hl hlq
  have h4 := hx.1
  have hh : r = 4 ∨ r = 5 := by omega
  rcases hh with rfl | rfl
  · exact split_orthogonal_rank_four_cross_contribution_lt hx hl hlq
  · exact split_orthogonal_five_cross_contribution_lt hx hl hlq

/-- Uniform strict defining-prime dominance for every admissible minus-D formula. -/
theorem minus_orthogonal_cross_contribution_lt {r q l : ℕ}
    (hx : Admissible (.Dminus r q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dminus r q)).factorization l < q ^ (r * (r - 1)) := by
  by_cases hr : 6 ≤ r
  · exact minus_orthogonal_cross_contribution_lt_of_six_le hx hr hl hlq
  have h4 := hx.1
  have hh : r = 4 ∨ r = 5 := by omega
  rcases hh with rfl | rfl
  · exact minus_orthogonal_rank_four_cross_contribution_lt hx hl hlq
  · exact minus_orthogonal_five_cross_contribution_lt hx hl hlq

end Atlas.OrderArithmetic

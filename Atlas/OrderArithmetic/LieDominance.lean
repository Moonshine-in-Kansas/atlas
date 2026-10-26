import Atlas.OrderArithmetic.SecondIndexBounds
import Atlas.OrderArithmetic.ClassicalDominance
import Atlas.OrderArithmetic.OrthogonalDominance
import Atlas.OrderArithmetic.UnitaryHigherDominance
import Atlas.OrderArithmetic.UnitaryFourDominance
import Atlas.OrderArithmetic.DominanceReduction

namespace Atlas.OrderArithmetic

/-- All ordinary Lie formulas have strict defining-prime dominance outside
rank one and the two explicitly isolated small unitary parameters. -/
theorem lie_cross_contribution_lt {x : RawEntry} {l : ℕ}
    (hx : Admissible x) (hLie : IsLie x)
    (hn2 : ∀ q : ℕ, x ≠ .linear 2 q)
    (hn33 : x ≠ .unitary 3 3) (hn42 : x ≠ .unitary 4 2)
    (hl : l.Prime) (hlq : ¬ l ∣ fieldSize x) :
    l ^ (order x).factorization l < fieldSize x ^ characteristicExponent x := by
  have hcases : IsClassicalLie x ∨ IsExceptionalLie x := by
    cases x <;> simp_all [IsLie, IsClassicalLie, IsExceptionalLie]
  rcases hcases with hc | he
  · cases x with
    | linear d q =>
      have hd : 3 ≤ d := by
        have hd2 := hx.1
        have hh := hn2 q
        by_contra hh'; have : d = 2 := by omega
        exact hh (by rw [this])
      exact linear_cross_contribution_lt_of_three_le hx hd hl hlq
    | unitary d q =>
      by_cases hd5 : 5 ≤ d
      · exact unitary_cross_contribution_lt_of_five_le hx hd5 hl hlq
      have hd3 := hx.1
      have hd : d = 3 ∨ d = 4 := by omega
      rcases hd with rfl | rfl
      · have hq : q ≠ 3 := by intro h; apply hn33; rw [h]
        exact unitary_three_cross_contribution_lt hx hq hl hlq
      · have hq : q ≠ 2 := by intro h; apply hn42; rw [h]
        exact unitary_four_cross_contribution_lt hx hq hl hlq
    | B r q => exact odd_orthogonal_cross_contribution_lt hx hl hlq
    | C r q => exact symplectic_cross_contribution_lt hx hl hlq
    | Dplus r q => exact split_orthogonal_cross_contribution_lt hx hl hlq
    | Dminus r q => exact minus_orthogonal_cross_contribution_lt hx hl hlq
    | _ => simp_all [IsClassicalLie]
  · exact exceptional_characteristic_dominance hx he hl hlq

end Atlas.OrderArithmetic

import Atlas.OrderArithmetic.HigherRankTwoDominance

namespace Atlas.OrderArithmetic

private theorem odd_of_two_not_dvd {q : ℕ} (h : ¬ 2 ∣ q) : Odd q := by
  apply Nat.odd_iff.mpr
  have hm := Nat.mod_lt q (by decide : 0 < 2)
  by_contra hn
  exact h (Nat.dvd_of_mod_eq_zero (by omega))

/-- Every cross-prime contribution is smaller than the characteristic part
for linear dimension at least eight, in every field characteristic. -/
theorem linear_cross_contribution_lt_of_eight_le {d q l : ℕ}
    (hx : Admissible (.linear d q)) (hd : 8 ≤ d)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  by_cases h2 : l = 2
  · subst l
    exact linear_two_contribution_lt_of_eight_le hx (odd_of_two_not_dvd hlq) hd
  · exact linear_odd_cross_contribution_lt_of_six_le hx (by omega) hl h2 hlq

/-- Every cross-prime contribution is smaller than the characteristic part
for C-rank at least five, in every field characteristic. -/
theorem symplectic_cross_contribution_lt_of_five_le {r q l : ℕ}
    (hx : Admissible (.C r q)) (hr : 5 ≤ r)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.C r q)).factorization l < q ^ (r ^ 2) := by
  by_cases h2 : l = 2
  · subst l
    exact symplectic_two_contribution_lt_of_four_le hx (odd_of_two_not_dvd hlq) (by omega)
  · exact symplectic_odd_cross_contribution_lt_of_five_le hx hr hl h2 hlq

theorem odd_orthogonal_cross_contribution_lt_of_five_le {r q l : ℕ}
    (hx : Admissible (.B r q)) (hr : 5 ≤ r)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.B r q)).factorization l < q ^ (r ^ 2) := by
  rw [order_B_eq_C]
  exact symplectic_cross_contribution_lt_of_five_le hx hr hl hlq

end Atlas.OrderArithmetic

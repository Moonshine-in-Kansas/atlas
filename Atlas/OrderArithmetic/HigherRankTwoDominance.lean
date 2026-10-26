import Atlas.OrderArithmetic.TwoAdicAccumulation

namespace Atlas.OrderArithmetic

private theorem odd_not_two_dvd {q : ℕ} (ho : Odd q) : ¬ 2 ∣ q := by
  intro hd
  have := Nat.mod_eq_zero_of_dvd hd
  have := Nat.odd_iff.mp ho
  omega

/-- Uniform binary contribution bound for an odd-field linear order. -/
theorem linear_two_contribution_le {d q : ℕ}
    (hx : Admissible (.linear d q)) (ho : Odd q) :
    2 ^ (order (.linear d q)).factorization 2 ≤ q ^ (3 * d) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hdres := cross_prime_order_contribution_dvd_residual hx (by trivial)
    Nat.prime_two (odd_not_two_dvd ho)
  have hdminus : 2 ^ (order (.linear d q)).factorization 2 ∣
      ∏ i ∈ Finset.Icc 1 d, (q ^ i - 1) := by
    apply hdres.trans
    change (∏ i ∈ Finset.Icc 2 d, (q ^ i - 1)) ∣ _
    apply Finset.prod_dvd_prod_of_subset
    intro i hi
    have hh := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  have hd := hdminus.trans (minus_segment_dvd_even_segment q d)
  have hv := (Nat.prime_two.pow_dvd_iff_le_factorization
    (even_minus_segment_ne_zero hq d)).mp hd
  exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hv).trans
    (two_contribution_even_segment_le hq ho d)

/-- Binary cross-contributions are strictly dominated in odd-field linear
dimension at least eight. -/
theorem linear_two_contribution_lt_of_eight_le {d q : ℕ}
    (hx : Admissible (.linear d q)) (ho : Odd q) (hd : 8 ≤ d) :
    2 ^ (order (.linear d q)).factorization 2 < q ^ (d * (d - 1) / 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hexp : 3 * d < d * (d - 1) / 2 := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hpoly : 6 * d + 2 ≤ d * (d - 1) := by nlinarith
    omega
  exact (linear_two_contribution_le hx ho).trans_lt
    ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr hexp)

/-- Uniform binary contribution bound for the actual C-family formula. -/
theorem symplectic_two_contribution_le {r q : ℕ}
    (hx : Admissible (.C r q)) (ho : Odd q) :
    2 ^ (order (.C r q)).factorization 2 ≤ q ^ (3 * r) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hd := cross_prime_order_contribution_dvd_residual hx (by trivial)
    Nat.prime_two (odd_not_two_dvd ho)
  change 2 ^ (order (.C r q)).factorization 2 ∣
    ∏ i ∈ Finset.Icc 1 r, (q ^ (2 * i) - 1) at hd
  have hv := (Nat.prime_two.pow_dvd_iff_le_factorization
    (even_minus_segment_ne_zero hq r)).mp hd
  exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hv).trans
    (two_contribution_even_segment_le hq ho r)

/-- Binary cross-contributions are strictly dominated in C-rank at least four. -/
theorem symplectic_two_contribution_lt_of_four_le {r q : ℕ}
    (hx : Admissible (.C r q)) (ho : Odd q) (hr : 4 ≤ r) :
    2 ^ (order (.C r q)).factorization 2 < q ^ (r ^ 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  exact (symplectic_two_contribution_le hx ho).trans_lt
    ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by nlinarith : 3 * r < r ^ 2))

theorem odd_orthogonal_two_contribution_lt_of_four_le {r q : ℕ}
    (hx : Admissible (.B r q)) (ho : Odd q) (hr : 4 ≤ r) :
    2 ^ (order (.B r q)).factorization 2 < q ^ (r ^ 2) := by
  rw [order_B_eq_C]
  exact symplectic_two_contribution_lt_of_four_le hx ho hr

end Atlas.OrderArithmetic

import Atlas.OrderArithmetic.ValuationSupport

namespace Atlas.OrderArithmetic

/-- Removing the characteristic factor and the central quotient cannot enlarge
a cross-prime contribution beyond the literal residual. -/
theorem cross_prime_order_contribution_dvd_residual {x : RawEntry} {l : ℕ}
    (hx : Admissible x) (hLie : IsLie x) (hl : l.Prime)
    (hlq : ¬ l ∣ fieldSize x) :
    l ^ (order x).factorization l ∣ residual x := by
  have hN : order x ≠ 0 := (lie_order_pos hx hLie).ne'
  have hdN : l ^ (order x).factorization l ∣ order x :=
    (hl.pow_dvd_iff_le_factorization hN).mpr le_rfl
  have hdnum : order x ∣ numerator x := by
    rw [lie_order_eq hLie]
    exact Nat.div_dvd_of_dvd (denominator_dvd_numerator hx)
  have hn : ¬ l ∣ fieldSize x ^ characteristicExponent x :=
    fun hh => hlq (hl.dvd_of_dvd_pow hh)
  exact hl.prime.pow_dvd_of_dvd_mul_left _ hn (hdN.trans hdnum)

private theorem minus_segment_ne_zero {q : ℕ} (hq : 2 ≤ q) (d : ℕ) :
    (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hpow : q ≤ q ^ i := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) hi1
  omega

/-- The literal linear order has odd cross-prime contribution at most q^(2d). -/
theorem linear_odd_cross_contribution_le {d q l : ℕ}
    (hx : Admissible (.linear d q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hlq : ¬ l ∣ q) :
    l ^ (order (.linear d q)).factorization l ≤ q ^ (2 * d) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hdres := cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq
  have hdsegment : l ^ (order (.linear d q)).factorization l ∣
      ∏ i ∈ Finset.Icc 1 d, (q ^ i - 1) := by
    apply hdres.trans
    change (∏ i ∈ Finset.Icc 2 d, (q ^ i - 1)) ∣ _
    apply Finset.prod_dvd_prod_of_subset
    intro i hi
    have hh := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  have hv := (hl.pow_dvd_iff_le_factorization (minus_segment_ne_zero hq d)).mp hdsegment
  exact (Nat.pow_le_pow_right hl.pos hv).trans
    (odd_cross_prime_minus_segment_contribution_le hl hl2 hq hlq d)

/-- Odd cross-primes are strictly dominated by the characteristic contribution
in every linear dimension at least six. -/
theorem linear_odd_cross_contribution_lt_of_six_le {d q l : ℕ}
    (hx : Admissible (.linear d q)) (hd : 6 ≤ d)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hexp : 2 * d < d * (d - 1) / 2 := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hpoly : 4 * d + 2 ≤ d * (d - 1) := by nlinarith
    omega
  exact (linear_odd_cross_contribution_le hx hl hl2 hlq).trans_lt
    ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr hexp)

/-- The literal C-family residual is a minus segment in base q². -/
theorem symplectic_odd_cross_contribution_le {r q l : ℕ}
    (hx : Admissible (.C r q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hlq : ¬ l ∣ q) :
    l ^ (order (.C r q)).factorization l ≤ q ^ (4 * r) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have hn : ¬ l ∣ q ^ 2 := fun hh => hlq (hl.dvd_of_dvd_pow hh)
  have hdres := cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq
  have hdsegment : l ^ (order (.C r q)).factorization l ∣
      ∏ i ∈ Finset.Icc 1 r, ((q ^ 2) ^ i - 1) := by
    simpa only [residual, pow_mul] using hdres
  have hv := (hl.pow_dvd_iff_le_factorization (minus_segment_ne_zero hq2 r)).mp hdsegment
  have hh := (Nat.pow_le_pow_right hl.pos hv).trans
    (odd_cross_prime_minus_segment_contribution_le hl hl2 hq2 hn r)
  have hpow : (q ^ 2) ^ (2 * r) = q ^ (4 * r) := by
    rw [← pow_mul]
    congr 1
    omega
  simpa only [hpow] using hh

/-- Odd cross-primes are strictly dominated in C-rank at least five. -/
theorem symplectic_odd_cross_contribution_lt_of_five_le {r q l : ℕ}
    (hx : Admissible (.C r q)) (hr : 5 ≤ r)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q) :
    l ^ (order (.C r q)).factorization l < q ^ (r ^ 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  exact (symplectic_odd_cross_contribution_le hx hl hl2 hlq).trans_lt
    ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by nlinarith : 4 * r < r ^ 2))

/-- The identical B/C literal order formulas share the odd-prime rank bound. -/
theorem odd_orthogonal_odd_cross_contribution_lt_of_five_le {r q l : ℕ}
    (hx : Admissible (.B r q)) (hr : 5 ≤ r)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q) :
    l ^ (order (.B r q)).factorization l < q ^ (r ^ 2) := by
  rw [order_B_eq_C]
  exact symplectic_odd_cross_contribution_lt_of_five_le hx hr hl hl2 hlq

end Atlas.OrderArithmetic

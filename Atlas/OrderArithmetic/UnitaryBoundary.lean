import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal
import Atlas.OrderArithmetic.StrictOddSegment

namespace Atlas.OrderArithmetic

/-- Strict odd-prime control at the boundary of the coarse unitary estimate. -/
theorem unitary_odd_cross_contribution_lt_four_dimension {d q l : ℕ}
    (hx : Admissible (.unitary d q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hlq : ¬ l ∣ q) :
    l ^ (order (.unitary d q)).factorization l < q ^ (4 * d) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hd : 3 ≤ d := hx.1
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have hh := cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq
    (even_minus_segment_ne_zero hq d) (unitary_residual_dvd_even_segment hq)
  have hb := odd_cross_prime_minus_segment_contribution_lt (d := d) hl hl2 hq2
    (fun hd => hlq (hl.dvd_of_dvd_pow hd)) (by omega)
  have hp : (q ^ 2) ^ (2 * d) = q ^ (4 * d) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hp] at hb
  have hb' : l ^ (∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1)).factorization l < q ^ (4 * d) := by
    simpa only [pow_mul] using hb
  exact hh.trans_lt hb'

/-- Every cross-prime is strictly dominated in unitary dimension at least
nine; the equality of coarse exponents at dimension nine is handled strictly. -/
theorem unitary_cross_contribution_lt_of_nine_le {d q l : ℕ}
    (hx : Admissible (.unitary d q)) (hd : 9 ≤ d)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.unitary d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have he : 4 * d ≤ d * (d - 1) / 2 := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hp : 8 * d ≤ d * (d - 1) := by nlinarith
    omega
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hlt : 3 * d < d * (d - 1) / 2 := by omega
    exact (unitary_two_contribution_le hx ho).trans_lt
      ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr hlt)
  · exact (unitary_odd_cross_contribution_lt_four_dimension hx hl hl2 hlq).trans_le
      (Nat.pow_le_pow_right (by omega : 0 < q) he)

end Atlas.OrderArithmetic

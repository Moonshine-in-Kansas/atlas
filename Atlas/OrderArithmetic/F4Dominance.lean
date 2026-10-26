import Atlas.OrderArithmetic.StrictOddSegment
import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal

namespace Atlas.OrderArithmetic

theorem F4_residual_dvd_even_segment (q : ℕ) :
    residual (.F4 q) ∣ ∏ i ∈ Finset.Icc 1 6, (q ^ (2 * i) - 1) := by
  have he : residual (.F4 q) =
      ∏ i ∈ ({1, 3, 4, 6} : Finset ℕ), (q ^ (2 * i) - 1) := by
    norm_num [residual, Finset.prod_insert]
  rw [he]
  apply Finset.prod_dvd_prod_of_subset
  decide

/-- Every cross-prime contribution to the literal F4 order is strictly below
its characteristic contribution, uniformly over all admissible field sizes. -/
theorem F4_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.F4 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.F4 q)).factorization l < q ^ 24 := by
  have hq : 2 ≤ q := primePower_two_le hx
  have htransfer := cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq
    (even_minus_segment_ne_zero hq 6) (F4_residual_dvd_even_segment q)
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hh : 2 ^ (∏ i ∈ Finset.Icc 1 6, (q ^ (2 * i) - 1)).factorization 2 ≤ q ^ 18 :=
      two_contribution_even_segment_le hq ho 6
    exact (htransfer.trans hh).trans_lt
      ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide : 18 < 24))
  · have hq2 : 2 ≤ q ^ 2 := by nlinarith
    have hh := odd_cross_prime_minus_segment_contribution_lt (d := 6) hl hl2 hq2
      (fun hh => hlq (hl.dvd_of_dvd_pow hh)) (by decide)
    have hh' : l ^ (∏ i ∈ Finset.Icc 1 6, (q ^ (2 * i) - 1)).factorization l < q ^ 24 := by
      simpa only [← pow_mul, show 2 * (2 * 6) = 24 by decide] using hh
    exact htransfer.trans_lt hh'

end Atlas.OrderArithmetic

import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal

namespace Atlas.OrderArithmetic

/-- A complete minus segment has a uniform cross-prime contribution bound;
the odd-prime estimate is stronger, but q^(3d) accommodates the binary case. -/
theorem cross_prime_minus_segment_contribution_le {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q) (d : ℕ) :
    l ^ (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)).factorization l ≤ q ^ (3 * d) := by
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hseg : (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      have hi1 := (Finset.mem_Icc.mp hi).1
      have hh : q ≤ q ^ i := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < q) hi1
      omega
    have hd : 2 ^ (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)).factorization 2 ∣
        ∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1) :=
      ((Nat.prime_two.pow_dvd_iff_le_factorization hseg).mpr le_rfl).trans
        (minus_segment_dvd_even_segment q d)
    have hv := (Nat.prime_two.pow_dvd_iff_le_factorization
      (even_minus_segment_ne_zero hq d)).mp hd
    exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hv).trans
      (two_contribution_even_segment_le hq ho d)
  · exact (odd_cross_prime_minus_segment_contribution_le hl hl2 hq hlq d).trans
      (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 2 * d ≤ 3 * d))

/-- A residual contained in a short minus segment is dominated whenever its
characteristic exponent is strictly larger than three times that length. -/
theorem cross_prime_contribution_lt_of_residual_dvd_segment {x : RawEntry} {l d : ℕ}
    (hx : Admissible x) (hLie : IsLie x) (hl : l.Prime)
    (hlq : ¬ l ∣ fieldSize x)
    (hd : residual x ∣ ∏ i ∈ Finset.Icc 1 d, (fieldSize x ^ i - 1))
    (hexp : 3 * d < characteristicExponent x) :
    l ^ (order x).factorization l < fieldSize x ^ characteristicExponent x := by
  have hq : 2 ≤ fieldSize x := primePower_two_le (lie_field_primePower hx hLie)
  have hseg : (∏ i ∈ Finset.Icc 1 d, (fieldSize x ^ i - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hh : fieldSize x ≤ fieldSize x ^ i := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < fieldSize x) hi1
    omega
  have hb := (cross_prime_contribution_le_of_residual_dvd hx hLie hl hlq hseg hd).trans
    (cross_prime_minus_segment_contribution_le hq hl hlq d)
  exact hb.trans_lt ((Nat.pow_lt_pow_iff_right (by omega : 1 < fieldSize x)).mpr hexp)

/-- Full cross-prime dominance for the literal E7 order formula. -/
theorem E7_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.E7 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.E7 q)).factorization l < q ^ 63 := by
  apply cross_prime_contribution_lt_of_residual_dvd_segment hx (by trivial) hl hlq
    (d := 18)
  · change (∏ i ∈ ({2, 6, 8, 10, 12, 14, 18} : Finset ℕ), (q ^ i - 1)) ∣
      ∏ i ∈ Finset.Icc 1 18, (q ^ i - 1)
    apply Finset.prod_dvd_prod_of_subset
    decide
  · norm_num [characteristicExponent]

/-- Full cross-prime dominance for the literal E8 order formula. -/
theorem E8_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.E8 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.E8 q)).factorization l < q ^ 120 := by
  apply cross_prime_contribution_lt_of_residual_dvd_segment hx (by trivial) hl hlq
    (d := 30)
  · change (∏ i ∈ ({2, 8, 12, 14, 18, 20, 24, 30} : Finset ℕ), (q ^ i - 1)) ∣
      ∏ i ∈ Finset.Icc 1 30, (q ^ i - 1)
    apply Finset.prod_dvd_prod_of_subset
    decide
  · norm_num [characteristicExponent]

end Atlas.OrderArithmetic

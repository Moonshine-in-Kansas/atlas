import Atlas.OrderArithmetic.TwoAdicAccumulation

namespace Atlas.OrderArithmetic

/-- The complete even segment has strictly smaller binary contribution than
q^(3d) whenever its length is positive. -/
theorem two_contribution_even_segment_lt {q d : ℕ} (hq : 2 ≤ q)
    (ho : Odd q) (hd : 1 ≤ d) :
    2 ^ (∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1)).factorization 2 < q ^ (3 * d) := by
  have hq2 : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hqs : 0 < q ^ 2 - 1 := by omega
  have hdiv : 2 ^ (q ^ 2 - 1).factorization 2 ∣ q ^ 2 - 1 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hqs.ne').mpr le_rfl
  have hb := Nat.le_of_dvd hqs hdiv
  rw [two_valuation_even_segment hq ho, pow_add]
  have hh : 2 ^ (d * (q ^ 2 - 1).factorization 2) =
      (2 ^ (q ^ 2 - 1).factorization 2) ^ d := by rw [← pow_mul, Nat.mul_comm]
  rw [hh]
  calc
    _ ≤ (q ^ 2 - 1) ^ d * 2 ^ d :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hb d) (factorial_prime_contribution_le Nat.prime_two d)
    _ < (q ^ 2) ^ d * 2 ^ d :=
      Nat.mul_lt_mul_of_pos_right
        (Nat.pow_lt_pow_left (by omega : q ^ 2 - 1 < q ^ 2) (by omega : d ≠ 0))
        (by positivity : 0 < 2 ^ d)
    _ ≤ (q ^ 2) ^ d * q ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq d)
    _ = q ^ (3 * d) := by rw [← pow_mul, ← pow_add]; congr 1; omega

/-- Any cross-characteristic prime power dividing a complete minus segment
is strictly smaller than q^(3d). This includes the binary prime. -/
theorem prime_power_dvd_minus_segment_lt {q l a d : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q) (hd : 1 ≤ d)
    (hdiv : l ^ a ∣ ∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)) : l ^ a < q ^ (3 * d) := by
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := by
      apply Nat.odd_iff.mpr
      have hb := Nat.mod_lt q (by decide : 0 < 2)
      have hn : q % 2 ≠ 0 := fun he => hlq (Nat.dvd_of_mod_eq_zero he)
      omega
    have heven := hdiv.trans (minus_segment_dvd_even_segment q d)
    have hv := (Nat.prime_two.pow_dvd_iff_le_factorization (even_minus_segment_ne_zero hq d)).mp heven
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hv).trans_lt
      (two_contribution_even_segment_lt hq ho hd)
  · have hn : (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      have hi1 := (Finset.mem_Icc.mp hi).1
      have hb : q ≤ q ^ i := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < q) hi1
      omega
    have hv := (hl.pow_dvd_iff_le_factorization hn).mp hdiv
    have hb := (Nat.pow_le_pow_right hl.pos hv).trans
      (odd_cross_prime_minus_segment_contribution_le hl hl2 hq hlq d)
    exact hb.trans_lt ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr
      (by omega : 2 * d < 3 * d))

/-- The six E₆ factors are contained in the complete minus segment through12. -/
theorem E6_residual_dvd_minus_segment (q : ℕ) :
    residual (.E6 q) ∣ ∏ i ∈ Finset.Icc 1 12, (q ^ i - 1) := by
  change (∏ i ∈ ({2, 5, 6, 8, 9, 12} : Finset ℕ), (q ^ i - 1)) ∣ _
  apply Finset.prod_dvd_prod_of_subset
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  apply Finset.mem_Icc.mpr
  omega

/-- Every cross-characteristic prime contribution is strictly below q³⁶ in
the E₆ order formula, including all effects of its central denominator. -/
theorem E6_cross_contribution_lt {q l : ℕ} (hx : Admissible (.E6 q))
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.E6 q)).factorization l < q ^ 36 := by
  have hq : 2 ≤ q := primePower_two_le hx
  have hdiv := (cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq).trans
    (E6_residual_dvd_minus_segment q)
  exact prime_power_dvd_minus_segment_lt hq hl hlq (by decide : 1 ≤ 12) hdiv

end Atlas.OrderArithmetic

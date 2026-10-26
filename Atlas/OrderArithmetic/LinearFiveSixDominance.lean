import Atlas.OrderArithmetic.StrictOddSegment
import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal
import Mathlib.Tactic.Zify

namespace Atlas.OrderArithmetic

/-- Strict odd-prime segment bounds improve the linear threshold to five. -/
theorem linear_odd_cross_contribution_lt_of_five_le {d q l : ℕ}
    (hx : Admissible (.linear d q)) (hd : 5 ≤ d)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hseg : (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hh : q ≤ q ^ i := by simpa using Nat.pow_le_pow_right (by omega : 0 < q) hi1
    omega
  have hdiv : residual (.linear d q) ∣ ∏ i ∈ Finset.Icc 1 d, (q ^ i - 1) := by
    apply Finset.prod_dvd_prod_of_subset
    intro i hi
    have hh := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  have hh := (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hseg hdiv).trans_lt
    (odd_cross_prime_minus_segment_contribution_lt hl hl2 hq hlq (by omega : 1 ≤ d))
  have he : 2 * d ≤ d * (d - 1) / 2 := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hp : 4 * d ≤ d * (d - 1) := by nlinarith
    omega
  exact hh.trans_le (Nat.pow_le_pow_right (by omega : 0 < q) he)

private theorem even_segment_three_two_bound {q : ℕ} (hq : 2 ≤ q) (ho : Odd q) :
    2 ^ (∏ i ∈ Finset.Icc 1 3, (q ^ (2 * i) - 1)).factorization 2 ≤
      2 * (q ^ 2 - 1) ^ 3 := by
  have h6 : (Nat.factorial 3).factorization 2 = 1 := by
    change (2 * 3).factorization 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply]
    norm_num [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hb : 2 ^ (q ^ 2 - 1).factorization 2 ≤ q ^ 2 - 1 := Nat.le_of_dvd (by omega)
    ((Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl)
  rw [two_valuation_even_segment hq ho, h6, pow_add]
  have hp : 2 ^ (3 * (q ^ 2 - 1).factorization 2) =
      (2 ^ (q ^ 2 - 1).factorization 2) ^ 3 := by rw [← pow_mul, Nat.mul_comm]
  rw [hp]
  have hh := Nat.pow_le_pow_left hb 3
  norm_num
  nlinarith

private theorem linear_six_odd_cofactor {q : ℕ} (ho : Odd q) :
    Odd ((q ^ 2 + q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) := by
  have h3 : Odd (q ^ 2 + q + 1) :=
    (ho.pow.add_odd ho).add_odd (by decide : Odd (1 : ℕ))
  have h5 : Odd (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) :=
    (((ho.pow.add_odd ho.pow).add_odd ho.pow).add_odd ho).add_odd (by decide : Odd (1 : ℕ))
  exact h3.mul h5

private theorem linear_six_residual_factor {q : ℕ} (hq : 2 ≤ q) :
    residual (.linear 6 q) =
      ((q - 1) ^ 2 * ∏ i ∈ Finset.Icc 1 3, (q ^ (2 * i) - 1)) *
        ((q ^ 2 + q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) := by
  have hs : ∀ n : ℕ, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ (by omega)
  norm_num [residual, Finset.prod_Icc_succ_top]
  zify [show 1 ≤ q by omega, hs 2, hs 3, hs 4, hs 5, hs 6]
  ring

/-- Binary contributions in linear dimensions five and six are bounded
using only three even factors and the odd cubic/quintic cofactors. -/
theorem linear_two_contribution_lt_ten_of_le_six {d q : ℕ}
    (hx : Admissible (.linear d q)) (hd : d ≤ 6) (ho : Odd q) :
    2 ^ (order (.linear d q)).factorization 2 < q ^ 10 := by
  have hq2 : 2 ≤ q := primePower_two_le hx.2.1
  have hq : 3 ≤ q := by have := Nat.odd_iff.mp ho; omega
  have hnq : ¬ 2 ∣ q := by
    intro hh
    have := Nat.mod_eq_zero_of_dvd hh
    have := Nat.odd_iff.mp ho
    omega
  have hdres := cross_prime_order_contribution_dvd_residual hx (by trivial) Nat.prime_two hnq
  have hsub : residual (.linear d q) ∣ residual (.linear 6 q) := by
    apply Finset.prod_dvd_prod_of_subset
    intro i hi
    have hh := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨hh.1, by omega⟩
  have hh := hdres.trans hsub
  rw [linear_six_residual_factor hq2] at hh
  have hno : ¬ 2 ∣ (q ^ 2 + q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) := by
    intro h
    have := Nat.mod_eq_zero_of_dvd h
    have := Nat.odd_iff.mp (linear_six_odd_cofactor ho)
    omega
  have hdA := Nat.prime_two.prime.pow_dvd_of_dvd_mul_right _ hno hh
  have hA : (q - 1) ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hB := even_minus_segment_ne_zero hq2 3
  have hv := (Nat.prime_two.pow_dvd_iff_le_factorization (mul_ne_zero hA hB)).mp hdA
  have hle := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hv
  rw [Nat.factorization_mul hA hB, Finsupp.add_apply, pow_add] at hle
  have hAbound : 2 ^ ((q - 1) ^ 2).factorization 2 ≤ (q - 1) ^ 2 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hA)
      ((Nat.prime_two.pow_dvd_iff_le_factorization hA).mpr le_rfl)
  have hb := hle.trans (Nat.mul_le_mul hAbound (even_segment_three_two_bound hq2 ho))
  have hsmall : (q - 1) ^ 2 * (2 * (q ^ 2 - 1) ^ 3) ≤ 2 * q ^ 8 := by
    have hm := Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le q 1) 2)
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.sub_le (q ^ 2) 1) 3))
    convert hm using 1 <;> ring
  have hlast : 2 * q ^ 8 < q ^ 10 := by
    have hqpow : 2 < q ^ 2 := by nlinarith
    have hm := Nat.mul_lt_mul_of_pos_right hqpow (pow_pos (by omega : 0 < q) 8)
    convert hm using 1 <;> ring
  exact (hb.trans hsmall).trans_lt hlast

theorem linear_five_six_cross_contribution_lt {d q l : ℕ}
    (hx : Admissible (.linear d q)) (hd : d = 5 ∨ d = 6)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  have hd5 : 5 ≤ d := by omega
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hh := linear_two_contribution_lt_ten_of_le_six hx (by omega) ho
    have he : 10 ≤ d * (d - 1) / 2 := by rcases hd with rfl | rfl <;> decide
    exact hh.trans_le (Nat.pow_le_pow_right (by have := primePower_two_le hx.2.1; omega) he)
  · exact linear_odd_cross_contribution_lt_of_five_le hx hd5 hl hl2 hlq

end Atlas.OrderArithmetic

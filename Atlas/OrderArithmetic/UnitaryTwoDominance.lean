import Atlas.OrderArithmetic.UnitaryThreeDominance
import Atlas.OrderArithmetic.UnitaryBoundary
import Atlas.OrderArithmetic.E6Dominance
import Mathlib.Tactic.Zify

namespace Atlas.OrderArithmetic

theorem unitary_two_contribution_lt_of_seven_le {d q : ℕ}
    (hx : Admissible (.unitary d q)) (ho : Odd q) (hd : 7 ≤ d) :
    2 ^ (order (.unitary d q)).factorization 2 < q ^ (d * (d - 1) / 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hn : ¬ 2 ∣ q := by
    intro hh
    have := Nat.mod_eq_zero_of_dvd hh
    have := Nat.odd_iff.mp ho
    omega
  have hb := (cross_prime_contribution_le_of_residual_dvd hx (by trivial) Nat.prime_two hn
    (even_minus_segment_ne_zero hq d) (unitary_residual_dvd_even_segment hq)).trans_lt
      (two_contribution_even_segment_lt hq ho (by omega : 1 ≤ d))
  have he : 3 * d ≤ d * (d - 1) / 2 := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hp : 6 * d ≤ d * (d - 1) := by nlinarith
    omega
  exact hb.trans_le (Nat.pow_le_pow_right (by omega : 0 < q) he)

private def unitaryQuinticCofactor (q : ℕ) : ℕ := q * (q - 1) * (q ^ 2 + 1) + 1

private theorem unitary_six_odd_cofactor (q : ℕ) :
    Odd (unitaryThreeCyclotomic q * unitaryQuinticCofactor q) := by
  have ho : Odd (unitaryQuinticCofactor q) :=
    ((Nat.even_mul_pred_self q).mul_right (q ^ 2 + 1)).add_odd (by decide : Odd (1 : ℕ))
  exact (unitaryThreeCyclotomic_odd q).mul ho

private theorem unitary_six_residual_factor {q : ℕ} (hq : 2 ≤ q) :
    residual (.unitary 6 q) =
      ((q + 1) ^ 2 * ∏ i ∈ Finset.Icc 1 3, (q ^ (2 * i) - 1)) *
        (unitaryThreeCyclotomic q * unitaryQuinticCofactor q) := by
  have hs : ∀ n : ℕ, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ (by omega)
  norm_num [residual, unitaryFactor, Finset.prod_Icc_succ_top]
  unfold unitaryThreeCyclotomic unitaryQuinticCofactor
  zify [show 1 ≤ q by omega, hs 2, hs 4, hs 6]
  ring

private theorem even_three_binary_bound {q : ℕ} (hq : 2 ≤ q) (ho : Odd q) :
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

theorem unitary_two_contribution_lt_ten_of_le_six {d q : ℕ}
    (hx : Admissible (.unitary d q)) (hd : d ≤ 6) (ho : Odd q) :
    2 ^ (order (.unitary d q)).factorization 2 < q ^ 10 := by
  have hq2 : 2 ≤ q := primePower_two_le hx.2.1
  have hq : 3 ≤ q := by have := Nat.odd_iff.mp ho; omega
  have hnq : ¬ 2 ∣ q := by
    intro hh
    have := Nat.mod_eq_zero_of_dvd hh
    have := Nat.odd_iff.mp ho
    omega
  have hdres := cross_prime_order_contribution_dvd_residual hx (by trivial) Nat.prime_two hnq
  have hsub : residual (.unitary d q) ∣ residual (.unitary 6 q) := by
    apply Finset.prod_dvd_prod_of_subset
    intro i hi
    have hh := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨hh.1, by omega⟩
  have hh := hdres.trans hsub
  rw [unitary_six_residual_factor hq2] at hh
  have hnC : ¬ 2 ∣ unitaryThreeCyclotomic q * unitaryQuinticCofactor q := by
    intro hc
    have := Nat.mod_eq_zero_of_dvd hc
    have := Nat.odd_iff.mp (unitary_six_odd_cofactor q)
    omega
  have hdA := Nat.prime_two.prime.pow_dvd_of_dvd_mul_right _ hnC hh
  have hA : (q + 1) ^ 2 ≠ 0 := by positivity
  have hB := even_minus_segment_ne_zero hq2 3
  have hv := (Nat.prime_two.pow_dvd_iff_le_factorization (mul_ne_zero hA hB)).mp hdA
  have hle := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hv
  rw [Nat.factorization_mul hA hB, Finsupp.add_apply, pow_add] at hle
  have hAbound : 2 ^ ((q + 1) ^ 2).factorization 2 ≤ (q + 1) ^ 2 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hA)
      ((Nat.prime_two.pow_dvd_iff_le_factorization hA).mpr le_rfl)
  have hb := hle.trans (Nat.mul_le_mul hAbound (even_three_binary_bound hq2 ho))
  have hp : 2 * (q + 1) ^ 2 < q ^ 4 := by
    have hq2' : 9 ≤ q ^ 2 := by nlinarith
    have hq4 : 9 * q ^ 2 ≤ q ^ 4 := by
      nlinarith [Nat.mul_le_mul_right (q ^ 2) hq2']
    nlinarith
  have hsmall : (q + 1) ^ 2 * (2 * (q ^ 2 - 1) ^ 3) ≤
      (2 * (q + 1) ^ 2) * q ^ 6 := by
    have hm := Nat.mul_le_mul_left (2 * (q + 1) ^ 2)
      (Nat.pow_le_pow_left (Nat.sub_le (q ^ 2) 1) 3)
    convert hm using 1 <;> ring
  have hlast : (2 * (q + 1) ^ 2) * q ^ 6 < q ^ 10 := by
    have hm := Nat.mul_lt_mul_of_pos_right hp (pow_pos (by omega : 0 < q) 6)
    convert hm using 1 <;> ring
  exact (hb.trans hsmall).trans_lt hlast

/-- The binary cross-prime is dominated in every unitary dimension at least five. -/
theorem unitary_two_contribution_lt_of_five_le {d q : ℕ}
    (hx : Admissible (.unitary d q)) (hd : 5 ≤ d) (ho : Odd q) :
    2 ^ (order (.unitary d q)).factorization 2 < q ^ (d * (d - 1) / 2) := by
  by_cases hd7 : 7 ≤ d
  · exact unitary_two_contribution_lt_of_seven_le hx ho hd7
  · have hb := unitary_two_contribution_lt_ten_of_le_six hx (by omega) ho
    have he : 10 ≤ d * (d - 1) / 2 := by
      have hd' : d = 5 ∨ d = 6 := by omega
      rcases hd' with rfl | rfl <;> decide
    exact hb.trans_le (Nat.pow_le_pow_right (by have := primePower_two_le hx.2.1; omega) he)

end Atlas.OrderArithmetic

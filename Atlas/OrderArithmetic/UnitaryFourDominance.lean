import Atlas.OrderArithmetic.LinearFourDominance
import Atlas.OrderArithmetic.UnitaryThreeDominance

namespace Atlas.OrderArithmetic

private theorem unitary_four_prime_contribution_mul_le {l A B : ℕ} (hl : l.Prime)
    (hA : 0 < A) (hB : 0 < B) :
    l ^ (A * B).factorization l ≤ A * l ^ B.factorization l := by
  have hd : l ^ A.factorization l ∣ A :=
    (hl.pow_dvd_iff_le_factorization hA.ne').mpr le_rfl
  rw [Nat.factorization_mul hA.ne' hB.ne', Finsupp.add_apply, pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hA hd)

theorem unitary_three_residual_three_contribution_le {q : ℕ}
    (hx : Admissible (.unitary 3 q)) (h3q : ¬ 3 ∣ q) :
    3 ^ (residual (.unitary 3 q)).factorization 3 ≤ 3 * (q + 1) ^ 2 := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hl : Nat.Prime 3 := by decide
  have hnR : residual (.unitary 3 q) ≠ 0 := by
    rw [unitary_three_residual_factor hq]
    exact mul_ne_zero (mul_ne_zero (by positivity) (by omega)) (by unfold unitaryThreeCyclotomic; omega)
  have hd : 3 ^ (residual (.unitary 3 q)).factorization 3 ∣ residual (.unitary 3 q) :=
    (hl.pow_dvd_iff_le_factorization hnR).mpr le_rfl
  have hdfact : 3 ^ (residual (.unitary 3 q)).factorization 3 ∣
      (q + 1) ^ 2 * (q - 1) * unitaryThreeCyclotomic q := by
    rwa [← unitary_three_residual_factor hq]
  clear hd
  have hd := hdfact
  have hBpos : 0 < unitaryThreeCyclotomic q := by unfold unitaryThreeCyclotomic; omega
  by_cases hm : 3 ∣ q - 1
  · have hp : ¬ 3 ∣ q + 1 := by
      intro hh
      have hd2 := Nat.dvd_sub hh hm
      have he : q + 1 - (q - 1) = 2 := by omega
      rw [he] at hd2
      norm_num at hd2
    have hb := unitaryThreeCyclotomic_minus_support hl hm
    have hd' := hl.prime.pow_dvd_of_dvd_mul_right _ hb hd
    have hd'' := hl.prime.pow_dvd_of_dvd_mul_left _
      (fun hh => hp (hl.dvd_of_dvd_pow hh)) hd'
    have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd''
    have hs := Nat.sub_le q 1
    nlinarith
  · have he : (q + 1) ^ 2 * (q - 1) * unitaryThreeCyclotomic q =
        ((q + 1) ^ 2 * unitaryThreeCyclotomic q) * (q - 1) := by ring
    rw [he] at hd
    have hd' := hl.prime.pow_dvd_of_dvd_mul_right _ hm hd
    have hv := (hl.pow_dvd_iff_le_factorization
      (mul_ne_zero (by positivity) hBpos.ne')).mp hd'
    have hb := (Nat.pow_le_pow_right hl.pos hv).trans
      (unitary_four_prime_contribution_mul_le hl (by positivity : 0 < (q + 1) ^ 2) hBpos)
    have h3 : 3 ^ (unitaryThreeCyclotomic q).factorization 3 ≤ 3 := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ))
        (unitaryThreeCyclotomic_three_valuation_le q)
    exact hb.trans (by nlinarith)

/-- Away from three, the U₃ central denominator does not change a
cross-characteristic valuation. -/
theorem unitary_three_order_residual_valuation {q l : ℕ}
    (hx : Admissible (.unitary 3 q)) (hl : l.Prime) (hl3 : l ≠ 3)
    (hlq : ¬ l ∣ q) :
    (order (.unitary 3 q)).factorization l = (residual (.unitary 3 q)).factorization l := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hR : residual (.unitary 3 q) ≠ 0 := by
    rw [unitary_three_residual_factor hq]
    exact mul_ne_zero (mul_ne_zero (by positivity) (by omega))
      (by unfold unitaryThreeCyclotomic; omega)
  have hden : ¬ l ∣ denominator (.unitary 3 q) := by
    intro hd
    have h3 : l ∣ 3 := hd.trans (Nat.gcd_dvd_left 3 (q + 1))
    exact hl3 ((Nat.prime_dvd_prime_iff_eq hl (by decide)).mp h3)
  have hpow : ¬ l ∣ q ^ 3 := fun hd => hlq (hl.dvd_of_dvd_pow hd)
  rw [lie_order_eq (by trivial : IsLie (.unitary 3 q)),
    Nat.factorization_div (denominator_dvd_numerator hx), Finsupp.tsub_apply,
    Nat.factorization_eq_zero_of_not_dvd hden, Nat.sub_zero]
  change (q ^ 3 * residual (.unitary 3 q)).factorization l = _
  rw [Nat.factorization_mul (pow_ne_zero 3 (by omega : q ≠ 0)) hR]
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpow, zero_add]

/-- Adjoining the fourth unitary factor introduces q²−1 and q²+1. -/
theorem unitary_four_residual_factor {q : ℕ} (hq : 2 ≤ q) :
    residual (.unitary 4 q) = residual (.unitary 3 q) * (q ^ 2 - 1) * (q ^ 2 + 1) := by
  have hs := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega : 1 ≤ q))
  have hs4 := Nat.sub_add_cancel (Nat.one_le_pow 4 q (by omega : 1 ≤ q))
  have he : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by nlinarith
  norm_num [residual, unitaryFactor, Finset.prod_Icc_succ_top, he]
  ring

/-- Odd primes in the new quadratic plus factor are absent from U₃'s residual. -/
theorem unitary_four_plus_prime_separation {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q)
    (hplus : l ∣ q ^ 2 + 1) : ¬ l ∣ residual (.unitary 3 q) := by
  have hnA := (linear_four_plus_prime_separation hq hl hl2 hlq hplus).1
  have hnminus : ¬ l ∣ q - 1 := fun hd => hnA (hd.trans (Nat.sub_one_dvd_pow_sub_one q 2))
  have hnplus : ¬ l ∣ q + 1 := by
    intro hd
    have hdiv : q + 1 ∣ q ^ 2 - 1 := by
      simpa [unitaryFactor] using unitary_factor_dvd_even_factor hq 1
    exact hnA (hd.trans hdiv)
  have hnC : ¬ l ∣ unitaryThreeCyclotomic q := by
    intro hd
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have hm := congrArg (fun t : ℕ => q * t) hs
    have he : q ^ 2 + 1 - unitaryThreeCyclotomic q = q := by
      unfold unitaryThreeCyclotomic
      have hb : q * (q - 1) + 1 ≤ q ^ 2 + 1 := by nlinarith
      have hh := Nat.sub_add_cancel hb
      nlinarith
    exact hlq (he ▸ Nat.dvd_sub hplus hd)
  rw [unitary_three_residual_factor hq]
  exact hl.prime.not_dvd_mul
    (hl.prime.not_dvd_mul (fun hd => hnplus (hl.dvd_of_dvd_pow hd)) hnminus) hnC

/-- Uniform U₄ dominance except the binary exceptional parameter. -/
theorem unitary_four_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.unitary 4 q)) (hqne : q ≠ 2)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.unitary 4 q)).factorization l < q ^ 6 := by
  have hq2 : 2 ≤ q := primePower_two_le hx.2.1
  have hq : 3 ≤ q := by omega
  have hx3 : Admissible (.unitary 3 q) := ⟨by decide, hx.2.1, by omega⟩
  have hA : q ^ 2 - 1 ≠ 0 := by
    have hpow : 1 < q ^ 2 := by nlinarith
    omega
  have hB : q ^ 2 + 1 ≠ 0 := by omega
  have hR : residual (.unitary 3 q) ≠ 0 := by
    rw [unitary_three_residual_factor hq2]
    exact mul_ne_zero (mul_ne_zero (by positivity) (by omega))
      (by unfold unitaryThreeCyclotomic; omega)
  have hR4 : residual (.unitary 4 q) ≠ 0 := by
    rw [unitary_four_residual_factor hq2]
    exact mul_ne_zero (mul_ne_zero hR hA) hB
  have hupper := cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hR4 (dvd_refl _)
  apply hupper.trans_lt
  have hCA : l ^ (q ^ 2 - 1).factorization l ≤ q ^ 2 :=
    (Nat.le_of_dvd (by omega : 0 < q ^ 2 - 1)
      ((hl.pow_dvd_iff_le_factorization hA).mpr le_rfl)).trans (Nat.sub_le _ _)
  have hfour : 4 * (q + 1) ^ 2 < q ^ 4 := by
    have hs : 3 * q ≤ q ^ 2 := by simpa [pow_two, mul_comm] using Nat.mul_le_mul_left q hq
    have hh := Nat.pow_lt_pow_left (by omega : 2 * (q + 1) < q ^ 2) (by decide : (2 : ℕ) ≠ 0)
    convert hh using 1 <;> ring
  rw [unitary_four_residual_factor hq2,
    Nat.factorization_mul (mul_ne_zero hR hA) hB,
    Nat.factorization_mul hR hA]
  simp only [Finsupp.add_apply, pow_add]
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hv := unitary_three_order_residual_valuation hx3 Nat.prime_two (by decide) hlq
    have hCR : 2 ^ (residual (.unitary 3 q)).factorization 2 ≤ 2 * (q + 1) ^ 2 := by
      rw [← hv]
      rcases unitary_three_two_contribution_bound hx3 ho with hh | hh
      · exact hh
      · have hs := Nat.sub_le q 1
        nlinarith
    rw [linear_four_plus_two_valuation ho, pow_one]
    have hb := Nat.mul_le_mul hCR hCA
    have hm := Nat.mul_le_mul_right 2 hb
    have hlt := Nat.mul_lt_mul_of_pos_right hfour (by positivity : 0 < q ^ 2)
    have he : q ^ 4 * q ^ 2 = q ^ 6 := by ring
    nlinarith
  by_cases hplus : l ∣ q ^ 2 + 1
  · have hnR := unitary_four_plus_prime_separation hq2 hl hl2 hlq hplus
    have hnA := (linear_four_plus_prime_separation hq2 hl hl2 hlq hplus).1
    rw [Nat.factorization_eq_zero_of_not_dvd hnR, Nat.factorization_eq_zero_of_not_dvd hnA]
    simp only [pow_zero, one_mul]
    have hb := Nat.le_of_dvd (Nat.succ_pos (q ^ 2))
      ((hl.pow_dvd_iff_le_factorization hB).mpr le_rfl)
    have hqpow : q ^ 4 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith
  rw [Nat.factorization_eq_zero_of_not_dvd hplus, pow_zero, mul_one]
  by_cases hl3 : l = 3
  · subst l
    have hCR := unitary_three_residual_three_contribution_le hx3 hlq
    have hb := Nat.mul_le_mul hCR hCA
    have hlt := Nat.mul_lt_mul_of_pos_right hfour (by positivity : 0 < q ^ 2)
    have he : q ^ 4 * q ^ 2 = q ^ 6 := by ring
    nlinarith
  · have hv := unitary_three_order_residual_valuation hx3 hl hl3 hlq
    have hCR : l ^ (residual (.unitary 3 q)).factorization l < q ^ 3 := by
      rw [← hv]
      exact unitary_three_odd_non_three_contribution_lt hx3 hl hl2 hl3 hlq
    calc
      _ < q ^ 3 * l ^ (q ^ 2 - 1).factorization l :=
        Nat.mul_lt_mul_of_pos_right hCR (pow_pos hl.pos _)
      _ ≤ q ^ 3 * q ^ 2 := Nat.mul_le_mul_left _ hCA
      _ = q ^ 5 := by ring
      _ < q ^ 6 := (Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide)

end Atlas.OrderArithmetic

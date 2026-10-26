import Atlas.OrderArithmetic.LinearThreeDominance

namespace Atlas.OrderArithmetic

/-- The linear dimension-three residual itself satisfies strict dominance;
this stronger fact can be reused before taking central quotients. -/
theorem linear_three_residual_cross_contribution_lt {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (residual (.linear 3 q)).factorization l < q ^ 3 := by
  by_cases hl2 : l = 2
  · subst l
    exact linear_three_residual_two_contribution_lt hq
      (Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh)))
  by_cases hl3 : l = 3
  · subst l
    exact linear_three_residual_three_contribution_lt hq
  have hn : residual (.linear 3 q) ≠ 0 := by
    rw [linear_three_residual_factor hq]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by omega)
  have hd : l ^ (residual (.linear 3 q)).factorization l ∣ residual (.linear 3 q) :=
    (hl.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have hdfact : l ^ (residual (.linear 3 q)).factorization l ∣
      (q - 1) ^ 2 * (q + 1) * (q ^ 2 + q + 1) := by
    rwa [← linear_three_residual_factor hq]
  have hq2 : 2 * q ≤ q ^ 2 := by simpa [pow_two, mul_comm] using Nat.mul_le_mul_left q hq
  have hq3 : 2 * q ^ 2 ≤ q ^ 3 := by
    calc
      _ ≤ q * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hq
      _ = q ^ 3 := by ring
  have hA : (q - 1) ^ 2 < q ^ 2 := Nat.pow_lt_pow_left (by omega) (by decide)
  rcases linear_three_prime_power_residual hq hl hl2 hl3 hdfact with ha | hb | hc
  · have hh := Nat.le_of_dvd (pow_pos (by omega : 0 < q - 1) 2) ha
    omega
  · have hh := Nat.le_of_dvd (Nat.succ_pos q) hb
    omega
  · have hh := Nat.le_of_dvd (Nat.succ_pos (q ^ 2 + q)) hc
    omega

private theorem square_minus_factor {q : ℕ} (hq : 1 ≤ q) :
    q ^ 2 - 1 = (q - 1) * (q + 1) := by
  have hs := Nat.sub_add_cancel hq
  have hs2 := Nat.sub_add_cancel (Nat.one_le_pow 2 q hq)
  nlinarith

/-- Adding the fourth linear factor introduces a quadratic minus and plus pair. -/
theorem linear_four_residual_factor {q : ℕ} (hq : 2 ≤ q) :
    residual (.linear 4 q) = residual (.linear 3 q) * (q ^ 2 - 1) * (q ^ 2 + 1) := by
  change (∏ i ∈ Finset.Icc 2 4, (q ^ i - 1)) = _
  rw [Finset.prod_Icc_succ_top (by decide : 2 ≤ 3 + 1)]
  change residual (.linear 3 q) * (q ^ 4 - 1) = _
  have he : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    simpa only [← pow_mul] using square_minus_factor (Nat.one_le_pow 2 q (by omega))
  rw [he]
  ring

/-- An odd prime in q²+1 is absent from both earlier linear residual factors. -/
theorem linear_four_plus_prime_separation {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q)
    (hplus : l ∣ q ^ 2 + 1) :
    ¬ l ∣ q ^ 2 - 1 ∧ ¬ l ∣ residual (.linear 3 q) := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
  have hnminus : ¬ l ∣ q ^ 2 - 1 := by
    intro hh
    have hd := Nat.dvd_sub hplus hh
    have he : q ^ 2 + 1 - (q ^ 2 - 1) = 2 := by omega
    rw [he] at hd
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd)
  have hnA : ¬ l ∣ q - 1 := fun hd => hnminus (hd.trans (Nat.sub_one_dvd_pow_sub_one q 2))
  have hnB : ¬ l ∣ q + 1 := by
    intro hd
    apply hnminus
    rw [square_minus_factor (by omega : 1 ≤ q)]
    exact dvd_mul_of_dvd_right hd _
  have hnC : ¬ l ∣ q ^ 2 + q + 1 := by
    intro hd
    have hh := Nat.dvd_sub hd hplus
    have he : q ^ 2 + q + 1 - (q ^ 2 + 1) = q := by omega
    exact hlq (he ▸ hh)
  refine ⟨hnminus, ?_⟩
  rw [linear_three_residual_factor hq]
  exact hl.prime.not_dvd_mul
    (hl.prime.not_dvd_mul (fun hd => hnA (hl.dvd_of_dvd_pow hd)) hnB) hnC

/-- The quadratic plus factor of an odd field has exactly one factor of two. -/
theorem linear_four_plus_two_valuation {q : ℕ} (ho : Odd q) :
    (q ^ 2 + 1).factorization 2 = 1 := by
  have hodd := Nat.odd_iff.mp ho
  have hc : q % 4 = 1 ∨ q % 4 = 3 := by omega
  have hs : q ^ 2 % 4 = 1 := by
    rcases hc with hc | hc
    all_goals norm_num [Nat.pow_mod, hc]
  have hm : (q ^ 2 + 1) % 4 = 2 := by omega
  have hn : q ^ 2 + 1 ≠ 0 := by omega
  have hd : 2 ∣ q ^ 2 + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hlo := (Nat.prime_two.dvd_iff_one_le_factorization hn).mp hd
  have hhi : ¬ 2 ≤ (q ^ 2 + 1).factorization 2 := by
    intro hh
    have hd := (Nat.prime_two.pow_dvd_iff_le_factorization hn).mpr hh
    have hz := Nat.mod_eq_zero_of_dvd hd
    norm_num at hz
    omega
  omega

/-- The full linear dimension-four residual is dominated in every
cross-characteristic prime, so the same holds after central division. -/
theorem linear_four_residual_cross_contribution_lt {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (residual (.linear 4 q)).factorization l < q ^ 6 := by
  have hq2 : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hA : q ^ 2 - 1 ≠ 0 := by omega
  have hB : q ^ 2 + 1 ≠ 0 := by omega
  have hR : residual (.linear 3 q) ≠ 0 := by
    rw [linear_three_residual_factor hq]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by omega)
  have hCR := linear_three_residual_cross_contribution_lt hq hl hlq
  have hCA := Nat.le_of_dvd (by omega : 0 < q ^ 2 - 1)
    ((hl.pow_dvd_iff_le_factorization hA).mpr le_rfl)
  have hprod : l ^ (residual (.linear 3 q)).factorization l *
      l ^ (q ^ 2 - 1).factorization l < q ^ 5 := by
    calc
      _ < q ^ 3 * l ^ (q ^ 2 - 1).factorization l :=
        Nat.mul_lt_mul_of_pos_right hCR (pow_pos hl.pos _)
      _ ≤ q ^ 3 * q ^ 2 := Nat.mul_le_mul_left _ (hCA.trans (Nat.sub_le _ _))
      _ = q ^ 5 := by rw [← pow_add]
  rw [linear_four_residual_factor hq,
    Nat.factorization_mul (mul_ne_zero hR hA) hB,
    Nat.factorization_mul hR hA]
  simp only [Finsupp.add_apply, pow_add]
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hq3 : 3 ≤ q := by have hm := Nat.odd_iff.mp ho; omega
    rw [linear_four_plus_two_valuation ho, pow_one]
    calc
      _ < q ^ 5 * 2 := Nat.mul_lt_mul_of_pos_right hprod (by decide)
      _ < q ^ 5 * q := Nat.mul_lt_mul_of_pos_left (by omega : 2 < q) (by positivity)
      _ = q ^ 6 := by ring
  by_cases hplus : l ∣ q ^ 2 + 1
  · obtain ⟨hnA, hnR⟩ := linear_four_plus_prime_separation hq hl hl2 hlq hplus
    rw [Nat.factorization_eq_zero_of_not_dvd hnA, Nat.factorization_eq_zero_of_not_dvd hnR]
    simp only [pow_zero, one_mul]
    have hCB := Nat.le_of_dvd (Nat.succ_pos (q ^ 2))
      ((hl.pow_dvd_iff_le_factorization hB).mpr le_rfl)
    have hpow : q ^ 2 + 1 < q ^ 6 := by
      have hp : 4 * q ^ 2 ≤ q ^ 4 := by
        have hb := Nat.mul_le_mul_right (q ^ 2) hq2
        convert hb using 1 <;> ring
      have hs := Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 4 ≤ 6)
      omega
    exact hCB.trans_lt hpow
  · rw [Nat.factorization_eq_zero_of_not_dvd hplus, pow_zero, mul_one]
    exact lt_trans hprod ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide : 5 < 6))

/-- Uniform strict characteristic dominance for the actual centrally divided
linear dimension-four order formula. -/
theorem linear_four_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.linear 4 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear 4 q)).factorization l < q ^ 6 := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hn : residual (.linear 4 q) ≠ 0 := by
    rw [linear_four_residual_factor hq, linear_three_residual_factor hq]
    have hq2 : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
    exact mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by omega))
      (by omega)) (by omega)
  exact (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hn (dvd_refl _)).trans_lt
    (linear_four_residual_cross_contribution_lt hq hl hlq)

end Atlas.OrderArithmetic

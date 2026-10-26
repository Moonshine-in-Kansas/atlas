import Atlas.OrderArithmetic.RankOneDominance

namespace Atlas.OrderArithmetic

/-- The cubic plus factor written without truncated subtraction in its quadratic factor. -/
theorem smallRee_cubic_factor (q : ℕ) (hq : 1 ≤ q) :
    q ^ 3 + 1 = (q + 1) * (q * (q - 1) + 1) := by
  have hs := Nat.sub_add_cancel hq
  have hm := congrArg (fun t : ℕ => q * t * (q + 1)) hs
  nlinarith

/-- A prime other than two or three cannot occur in two different small Ree
residual factors. Consequently its whole power occurs in a single factor. -/
theorem smallRee_odd_prime_power_residual {q l e : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hl2 : l ≠ 2) (hl3 : l ≠ 3)
    (hlq : ¬ l ∣ q) (hd : l ^ e ∣ (q ^ 3 + 1) * (q - 1)) :
    l ^ e ∣ q - 1 ∨ l ^ e ∣ q + 1 ∨ l ^ e ∣ q * (q - 1) + 1 := by
  have hAB : l ∣ q - 1 → ¬ l ∣ q + 1 := by
    intro hA hB
    have hh := Nat.dvd_sub hB hA
    have he : q + 1 - (q - 1) = 2 := by omega
    rw [he] at hh
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl (by decide)).mp hh)
  have hAC : l ∣ q - 1 → ¬ l ∣ q * (q - 1) + 1 := by
    intro hA hC
    have hmul : l ∣ q * (q - 1) := dvd_mul_of_dvd_right hA q
    have hh := Nat.dvd_sub hC hmul
    exact hl.not_dvd_one (by simpa using hh)
  have hBC : l ∣ q + 1 → ¬ l ∣ q * (q - 1) + 1 := by
    intro hB hC
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have he : (q + 1) ^ 2 - (q * (q - 1) + 1) = 3 * q := by
      have hm := congrArg (fun t : ℕ => q * t) hs
      have hbound : q * (q - 1) + 1 ≤ (q + 1) ^ 2 := by nlinarith
      have hsub := Nat.sub_add_cancel hbound
      nlinarith
    have hsq : l ∣ (q + 1) ^ 2 := hB.trans (dvd_pow_self _ (by decide))
    have hh := Nat.dvd_sub hsq hC
    rw [he] at hh
    have hthree : l ∣ 3 := (hl.dvd_mul.mp hh).resolve_right hlq
    exact hl3 ((Nat.prime_dvd_prime_iff_eq hl (by decide)).mp hthree)
  rw [smallRee_cubic_factor q (by omega)] at hd
  by_cases hA : l ∣ q - 1
  · apply Or.inl
    have hn : ¬ l ∣ (q + 1) * (q * (q - 1) + 1) :=
      hl.prime.not_dvd_mul (hAB hA) (hAC hA)
    exact hl.prime.pow_dvd_of_dvd_mul_left e hn hd
  · have hBCpow := hl.prime.pow_dvd_of_dvd_mul_right e hA hd
    by_cases hB : l ∣ q + 1
    · exact Or.inr (Or.inl (hl.prime.pow_dvd_of_dvd_mul_right e (hBC hB) hBCpow))
    · exact Or.inr (Or.inr (hl.prime.pow_dvd_of_dvd_mul_left e hB hBCpow))

/-- Odd cross-characteristic prime contributions are strictly below q³. -/
theorem smallRee_odd_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.smallRee q)) (hl : l.Prime) (hl2 : l ≠ 2) (hl3 : l ≠ 3) :
    l ^ (order (.smallRee q)).factorization l < q ^ 3 := by
  obtain ⟨m, hm, hqfield⟩ := hx
  have hq : 2 ≤ q := by
    have hb : 3 ^ 3 ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hqfield]
    omega
  have hpos : 0 < order (.smallRee q) :=
    lie_order_pos ⟨m, hm, hqfield⟩ (by trivial)
  have hlq : ¬ l ∣ q := by
    intro hh
    rw [hqfield] at hh
    exact hl3 (Nat.prime_eq_prime_of_dvd_pow hl (by decide : Nat.Prime 3) hh)
  have hlq3 : ¬ l ∣ q ^ 3 := fun hd => hlq (hl.dvd_of_dvd_pow hd)
  have hd : l ^ (order (.smallRee q)).factorization l ∣ order (.smallRee q) :=
    (hl.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  have hdfact : l ^ (order (.smallRee q)).factorization l ∣
      q ^ 3 * ((q ^ 3 + 1) * (q - 1)) := by
    convert hd using 1 <;> simp only [order, numerator, fieldSize,
      characteristicExponent, residual, denominator, Nat.div_one]
  have hres := hl.prime.pow_dvd_of_dvd_mul_left _ hlq3 hdfact
  have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
  have hmul := congrArg (fun t : ℕ => q * t) hs
  have hdouble : 2 * q ≤ q ^ 2 := by
    simpa [pow_two, mul_comm] using Nat.mul_le_mul_left q hq
  have hsq : q ^ 2 < q ^ 3 := by
    have : q ^ 2 < q ^ 2 * q := lt_mul_of_one_lt_right (by positivity) (by omega)
    simpa [pow_succ] using this
  have hquad : q * (q - 1) + 1 ≤ q ^ 2 := by nlinarith
  rcases smallRee_odd_prime_power_residual hq hl hl2 hl3 hlq hres with hA | hB | hC
  · have hb := Nat.le_of_dvd (by omega : 0 < q - 1) hA
    nlinarith
  · have hb := Nat.le_of_dvd (by omega : 0 < q + 1) hB
    nlinarith
  · exact (Nat.le_of_dvd (by positivity : 0 < q * (q - 1) + 1) hC).trans_lt
      (hquad.trans_lt hsq)

/-- Admissible small Ree field sizes are three modulo eight. -/
theorem smallRee_field_mod_eight {q : ℕ} (hx : Admissible (.smallRee q)) : q % 8 = 3 := by
  obtain ⟨m, hm, rfl⟩ := hx
  rw [pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

/-- The two-adic valuation of every admissible small Ree order is exactly three. -/
theorem smallRee_two_valuation {q : ℕ} (hx : Admissible (.smallRee q)) :
    (order (.smallRee q)).factorization 2 = 3 := by
  have hmod := smallRee_field_mod_eight hx
  have hq : 3 ≤ q := by omega
  have hcube : q ^ 3 % 8 = 3 := by rw [Nat.pow_mod, hmod]
  have hplus : (q ^ 3 + 1) % 8 = 4 := by omega
  have hminus : (q - 1) % 4 = 2 := by omega
  have hqnot : ¬ 2 ∣ q ^ 3 := by
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  have hvplus : (q ^ 3 + 1).factorization 2 = 2 := by
    have hd : 2 ^ 2 ∣ q ^ 3 + 1 := Nat.dvd_of_mod_eq_zero (by norm_num; omega)
    have hlo := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : q ^ 3 + 1 ≠ 0)).mp hd
    have hhi : ¬ 3 ≤ (q ^ 3 + 1).factorization 2 := by
      intro hh
      have hh := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : q ^ 3 + 1 ≠ 0)).mpr hh
      have hz := Nat.mod_eq_zero_of_dvd hh
      norm_num at hz
      omega
    omega
  have hvminus : (q - 1).factorization 2 = 1 := by
    have hd : 2 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hlo := (Nat.prime_two.dvd_iff_one_le_factorization (by omega : q - 1 ≠ 0)).mp hd
    have hhi : ¬ 2 ≤ (q - 1).factorization 2 := by
      intro hh
      have hh := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : q - 1 ≠ 0)).mpr hh
      have hz := Nat.mod_eq_zero_of_dvd hh
      norm_num at hz
      omega
    omega
  simp only [order, numerator, fieldSize, characteristicExponent, residual,
    denominator, Nat.div_one]
  rw [Nat.factorization_mul (pow_ne_zero 3 (by omega : q ≠ 0))
      (mul_ne_zero (by omega : q ^ 3 + 1 ≠ 0) (by omega : q - 1 ≠ 0)),
    Nat.factorization_mul (by positivity : q ^ 3 + 1 ≠ 0) (by omega : q - 1 ≠ 0)]
  norm_num only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqnot, hvplus, hvminus]

/-- Every cross-characteristic prime contributes strictly less than the
characteristic contribution q³ in an admissible small Ree order. -/
theorem smallRee_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.smallRee q)) (hl : l.Prime) (hl3 : l ≠ 3) :
    l ^ (order (.smallRee q)).factorization l < q ^ 3 := by
  by_cases hl2 : l = 2
  · subst l
    rw [smallRee_two_valuation hx]
    have hmod := smallRee_field_mod_eight hx
    have hq : 3 ≤ q := by omega
    have hsq : 9 ≤ q ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hq hq
    have hcube : 27 ≤ q ^ 3 := by
      have hb := Nat.mul_le_mul hsq hq
      simpa [pow_succ] using hb
    norm_num
    omega
  · exact smallRee_odd_cross_contribution_lt hx hl hl2 hl3

end Atlas.OrderArithmetic

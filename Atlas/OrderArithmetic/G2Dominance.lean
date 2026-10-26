import Atlas.OrderArithmetic.RankOneDominance

namespace Atlas.OrderArithmetic

/-- The split G₂ residual separates into a squared quadratic factor and one
quartic factor; no cyclotomic valuation theorem is needed for this identity. -/
theorem g2_residual_factor {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 6 - 1) * (q ^ 2 - 1) =
      (q ^ 2 - 1) ^ 2 * (q ^ 4 + q ^ 2 + 1) := by
  have hs := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega : 1 ≤ q))
  have hs6 := Nat.sub_add_cancel (Nat.one_le_pow 6 q (by omega : 1 ≤ q))
  have hm := congrArg (fun t : ℕ => t * (q ^ 4 + q ^ 2 + 1)) hs
  have he : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by nlinarith
  rw [he]
  ring

/-- Only the prime three can occur in both displayed residual factors. -/
theorem g2_factor_prime_separation {q l : ℕ} (hq : 2 ≤ q)
    (hl : l.Prime) (hl3 : l ≠ 3) (ha : l ∣ q ^ 2 - 1) :
    ¬ l ∣ q ^ 4 + q ^ 2 + 1 := by
  intro hb
  have hs := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega : 1 ≤ q))
  have hm := congrArg (fun t : ℕ => t * (q ^ 2 + 2)) hs
  have he : q ^ 4 + q ^ 2 + 1 = (q ^ 2 - 1) * (q ^ 2 + 2) + 3 := by nlinarith
  have hh := Nat.dvd_sub hb (dvd_mul_of_dvd_left ha (q ^ 2 + 2))
  rw [he, Nat.add_sub_cancel_left] at hh
  exact hl3 ((Nat.prime_dvd_prime_iff_eq hl (by decide)).mp hh)

/-- Away from characteristic three, the quartic G₂ factor has exactly one
factor of three; reduction modulo nine proves the complete assertion. -/
theorem g2_quartic_three_valuation {q : ℕ} (hq3 : ¬ 3 ∣ q) :
    (q ^ 4 + q ^ 2 + 1).factorization 3 = 1 := by
  have hn : q % 3 ≠ 0 := fun he => hq3 (Nat.dvd_of_mod_eq_zero he)
  have h9 := Nat.mod_lt q (by decide : 0 < 9)
  have hc : q % 9 = 1 ∨ q % 9 = 2 ∨ q % 9 = 4 ∨
      q % 9 = 5 ∨ q % 9 = 7 ∨ q % 9 = 8 := by omega
  have hm : (q ^ 4 + q ^ 2 + 1) % 9 = 3 := by
    rcases hc with hc | hc | hc | hc | hc | hc
    all_goals norm_num [Nat.add_mod, Nat.pow_mod, hc]
  have hpos : q ^ 4 + q ^ 2 + 1 ≠ 0 := by omega
  have hd : 3 ∣ q ^ 4 + q ^ 2 + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hlo := ((by decide : Nat.Prime 3).dvd_iff_one_le_factorization hpos).mp hd
  have hhi : ¬ 2 ≤ (q ^ 4 + q ^ 2 + 1).factorization 3 := by
    intro hh
    have hh := ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization hpos).mpr hh
    have hz := Nat.mod_eq_zero_of_dvd hh
    norm_num at hz
    omega
  omega

/-- Every cross-characteristic prime contributes strictly less than q⁶ to an
admissible split G₂ order. The characteristic exclusion is the direct condition
that the prime does not divide the field size. -/
theorem g2_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.G2 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.G2 q)).factorization l < q ^ 6 := by
  have hq : 3 ≤ q := hx.2
  have hq2 : 9 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hApos : q ^ 2 - 1 ≠ 0 := by omega
  have hBpos : q ^ 4 + q ^ 2 + 1 ≠ 0 := by omega
  have horder : order (.G2 q) = q ^ 6 *
      ((q ^ 2 - 1) ^ 2 * (q ^ 4 + q ^ 2 + 1)) := by
    simp only [order, numerator, fieldSize, characteristicExponent, residual,
      denominator, Nat.div_one]
    rw [g2_residual_factor (by omega)]
  have hlq6 : ¬ l ∣ q ^ 6 := fun hd => hlq (hl.dvd_of_dvd_pow hd)
  have hNpos := lie_order_pos hx (by trivial : IsLie (.G2 q))
  have hdiv : l ^ (order (.G2 q)).factorization l ∣ order (.G2 q) :=
    (hl.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  have hdfact : l ^ (order (.G2 q)).factorization l ∣ q ^ 6 *
      ((q ^ 2 - 1) ^ 2 * (q ^ 4 + q ^ 2 + 1)) := by
    rwa [← horder]
  have hres := hl.prime.pow_dvd_of_dvd_mul_left _ hlq6 hdfact
  have hA_lt : (q ^ 2 - 1) ^ 2 < q ^ 4 := by
    have hb := Nat.pow_lt_pow_left (by omega : q ^ 2 - 1 < q ^ 2) (by decide : (2 : ℕ) ≠ 0)
    simpa [← pow_mul] using hb
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hq4pos : 0 < q ^ 4 := by positivity
  have hscale : 9 * q ^ 4 ≤ q ^ 6 := by
    have hb := Nat.mul_le_mul_right (q ^ 4) hq2
    convert hb using 1 <;> ring
  by_cases hl3 : l = 3
  · subst l
    have hv : (order (.G2 q)).factorization 3 = 2 * (q ^ 2 - 1).factorization 3 + 1 := by
      rw [horder, Nat.factorization_mul (by positivity : q ^ 6 ≠ 0)
        (mul_ne_zero (pow_ne_zero 2 hApos) hBpos),
        Nat.factorization_mul (pow_ne_zero 2 hApos) hBpos]
      simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hlq,
        zero_add, mul_zero, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        g2_quartic_three_valuation hlq]
    have hd : 3 ^ (q ^ 2 - 1).factorization 3 ∣ q ^ 2 - 1 :=
      ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization hApos).mpr le_rfl
    have hb := Nat.le_of_dvd (by omega : 0 < q ^ 2 - 1) hd
    have hbsq := Nat.mul_le_mul hb hb
    rw [hv, pow_add, pow_one, Nat.mul_comm 2 _, pow_mul]
    have he : (3 ^ (q ^ 2 - 1).factorization 3) ^ 2 ≤ (q ^ 2 - 1) ^ 2 := by
      simpa [pow_two] using hbsq
    nlinarith
  · by_cases ha : l ∣ q ^ 2 - 1
    · have hn := g2_factor_prime_separation (by omega : 2 ≤ q) hl hl3 ha
      have hd := hl.prime.pow_dvd_of_dvd_mul_right _ hn hres
      have hb := Nat.le_of_dvd (pow_pos (by omega : 0 < q ^ 2 - 1) 2) hd
      omega
    · have hn : ¬ l ∣ (q ^ 2 - 1) ^ 2 := fun hd => ha (hl.dvd_of_dvd_pow hd)
      have hd := hl.prime.pow_dvd_of_dvd_mul_left _ hn hres
      have hb := Nat.le_of_dvd (by omega : 0 < q ^ 4 + q ^ 2 + 1) hd
      omega

end Atlas.OrderArithmetic

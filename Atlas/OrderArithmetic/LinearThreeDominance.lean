import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal
import Atlas.OrderArithmetic.RankOneTwoAdic

namespace Atlas.OrderArithmetic

/-- Exact factorization of the literal linear dimension-three residual. -/
theorem linear_three_residual_factor {q : ℕ} (hq : 2 ≤ q) :
    residual (.linear 3 q) = (q - 1) ^ 2 * (q + 1) * (q ^ 2 + q + 1) := by
  have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
  have hs2 := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega))
  have hs3 := Nat.sub_add_cancel (Nat.one_le_pow 3 q (by omega))
  have hm := congrArg (fun t : ℕ => t * (q ^ 2 + q + 1)) hs
  have he2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by nlinarith
  have he3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by nlinarith
  norm_num [residual, Finset.prod_Icc_succ_top, he2, he3]
  ring

/-- The ternary contribution of Φ₃(q) is at most three for every integer q. -/
theorem linear_three_cyclotomic_three_valuation_le (q : ℕ) :
    (q ^ 2 + q + 1).factorization 3 ≤ 1 := by
  have hb := Nat.mod_lt q (by decide : 0 < 9)
  have hc : q % 9 = 0 ∨ q % 9 = 1 ∨ q % 9 = 2 ∨ q % 9 = 3 ∨
      q % 9 = 4 ∨ q % 9 = 5 ∨ q % 9 = 6 ∨ q % 9 = 7 ∨ q % 9 = 8 := by omega
  have hn : ¬ 9 ∣ q ^ 2 + q + 1 := by
    intro hd
    have hm := Nat.mod_eq_zero_of_dvd hd
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc
    all_goals norm_num [Nat.add_mod, Nat.pow_mod, hc] at hm
  by_contra hh
  have hd := ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization
    (by omega : q ^ 2 + q + 1 ≠ 0)).mpr (by omega : 2 ≤ (q ^ 2 + q + 1).factorization 3)
  exact hn (by simpa using hd)

/-- The cyclotomic factor is coprime to the upper adjacent factor. -/
theorem linear_three_upper_cyclotomic_separation {q l : ℕ} (hl : l.Prime)
    (hB : l ∣ q + 1) : ¬ l ∣ q ^ 2 + q + 1 := by
  intro hC
  have hm : l ∣ q * (q + 1) := dvd_mul_of_dvd_right hB q
  have he : q ^ 2 + q + 1 = q * (q + 1) + 1 := by ring
  rw [he] at hC
  exact hl.not_dvd_one (by simpa using Nat.dvd_sub hC hm)

/-- Away from three, the cyclotomic factor is also prime-separated from q−1. -/
theorem linear_three_lower_cyclotomic_separation {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hl3 : l ≠ 3)
    (hA : l ∣ q - 1) : ¬ l ∣ q ^ 2 + q + 1 := by
  intro hC
  have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
  have hm := congrArg (fun t : ℕ => t * (q + 2)) hs
  have he : q ^ 2 + q + 1 = (q - 1) * (q + 2) + 3 := by nlinarith
  rw [he] at hC
  have hd := Nat.dvd_sub hC (dvd_mul_of_dvd_left hA (q + 2))
  have hthree : l ∣ 3 := by simpa using hd
  exact hl3 ((Nat.prime_dvd_prime_iff_eq hl (by decide)).mp hthree)

private theorem linear_three_adjacent_separation {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hl2 : l ≠ 2)
    (hA : l ∣ q - 1) : ¬ l ∣ q + 1 := by
  intro hB
  have hd := Nat.dvd_sub hB hA
  have he : q + 1 - (q - 1) = 2 := by omega
  rw [he] at hd
  exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd)

/-- All residual contributions away from two and three lie in one factor. -/
theorem linear_three_prime_power_residual {q l e : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hl2 : l ≠ 2) (hl3 : l ≠ 3)
    (hd : l ^ e ∣ (q - 1) ^ 2 * (q + 1) * (q ^ 2 + q + 1)) :
    l ^ e ∣ (q - 1) ^ 2 ∨ l ^ e ∣ q + 1 ∨ l ^ e ∣ q ^ 2 + q + 1 := by
  by_cases ha : l ∣ q - 1
  · have hnB := linear_three_adjacent_separation hq hl hl2 ha
    have hnC := linear_three_lower_cyclotomic_separation hq hl hl3 ha
    exact Or.inl (hl.prime.pow_dvd_of_dvd_mul_right e hnB
      (hl.prime.pow_dvd_of_dvd_mul_right e hnC hd))
  · have hnA : ¬ l ∣ (q - 1) ^ 2 := fun hh => ha (hl.dvd_of_dvd_pow hh)
    by_cases hb : l ∣ q + 1
    · have hnC := linear_three_upper_cyclotomic_separation hl hb
      exact Or.inr (Or.inl (hl.prime.pow_dvd_of_dvd_mul_left e hnA
        (hl.prime.pow_dvd_of_dvd_mul_right e hnC hd)))
    · have hnAB := hl.prime.not_dvd_mul hnA hb
      exact Or.inr (Or.inr (hl.prime.pow_dvd_of_dvd_mul_left e hnAB hd))

/-- The full residual ternary contribution needs no cancellation by the
central denominator to be strictly below q³. -/
theorem linear_three_residual_three_contribution_lt {q : ℕ} (hq : 2 ≤ q) :
    3 ^ (residual (.linear 3 q)).factorization 3 < q ^ 3 := by
  have hp : Nat.Prime 3 := by decide
  have hA : q - 1 ≠ 0 := by omega
  have hB : q + 1 ≠ 0 := by omega
  have hC : q ^ 2 + q + 1 ≠ 0 := by omega
  by_cases hb : 3 ∣ q + 1
  · have hnA : ¬ 3 ∣ q - 1 := fun ha =>
      linear_three_adjacent_separation hq hp (by decide) ha hb
    have hnC := linear_three_upper_cyclotomic_separation hp hb
    rw [linear_three_residual_factor hq,
      Nat.factorization_mul (mul_ne_zero (pow_ne_zero 2 hA) hB) hC,
      Nat.factorization_mul (pow_ne_zero 2 hA) hB]
    simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hnA, Nat.factorization_eq_zero_of_not_dvd hnC,
      mul_zero, zero_add, add_zero]
    have hd : 3 ^ (q + 1).factorization 3 ∣ q + 1 :=
      (hp.pow_dvd_iff_le_factorization hB).mpr le_rfl
    have hle := Nat.le_of_dvd (by omega : 0 < q + 1) hd
    have hqpow : 4 * q ≤ q ^ 3 := by
      have hs : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
      simpa [pow_succ] using Nat.mul_le_mul_right q hs
    omega
  · rw [linear_three_residual_factor hq,
      Nat.factorization_mul (mul_ne_zero (pow_ne_zero 2 hA) hB) hC,
      Nat.factorization_mul (pow_ne_zero 2 hA) hB]
    simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hb, add_zero]
    have hd : 3 ^ (q - 1).factorization 3 ∣ q - 1 :=
      (hp.pow_dvd_iff_le_factorization hA).mpr le_rfl
    have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd
    have hcube : 3 * (q - 1) ^ 2 < q ^ 3 := by
      have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
      have hm := congrArg (fun t : ℕ => t ^ 3) hs
      have hpos : 0 < (q - 1) ^ 3 := pow_pos (by omega) 3
      nlinarith
    calc
      _ = (3 ^ (q - 1).factorization 3) ^ 2 *
          3 ^ (q ^ 2 + q + 1).factorization 3 := by rw [pow_add, Nat.mul_comm 2 _, pow_mul]
      _ ≤ (q - 1) ^ 2 * 3 := Nat.mul_le_mul (Nat.pow_le_pow_left hle 2)
        (by simpa using (Nat.pow_le_pow_right (by decide : 0 < 3)
          (linear_three_cyclotomic_three_valuation_le q)))
      _ < q ^ 3 := by simpa only [mul_comm] using hcube

/-- The binary residual contribution in odd characteristic is strictly below q³. -/
theorem linear_three_residual_two_contribution_lt {q : ℕ} (hq : 2 ≤ q) (ho : Odd q) :
    2 ^ (residual (.linear 3 q)).factorization 2 < q ^ 3 := by
  have hq3 : 3 ≤ q := by have hm := Nat.odd_iff.mp ho; omega
  have hA : q - 1 ≠ 0 := by omega
  have hB : q + 1 ≠ 0 := by omega
  have hC : q ^ 2 + q + 1 ≠ 0 := by omega
  have hnC : ¬ 2 ∣ q ^ 2 + q + 1 := by
    intro hd
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hodd := Nat.odd_iff.mp ho
    norm_num [Nat.add_mod, Nat.pow_mod, hodd] at hm
  rw [linear_three_residual_factor hq,
    Nat.factorization_mul (mul_ne_zero (pow_ne_zero 2 hA) hB) hC,
    Nat.factorization_mul (pow_ne_zero 2 hA) hB]
  simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_eq_zero_of_not_dvd hnC, add_zero]
  have hAle := Nat.le_of_dvd (by omega : 0 < q - 1)
    ((Nat.prime_two.pow_dvd_iff_le_factorization hA).mpr le_rfl)
  have hBle := Nat.le_of_dvd (by omega : 0 < q + 1)
    ((Nat.prime_two.pow_dvd_iff_le_factorization hB).mpr le_rfl)
  have hsq : 9 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq3 hq3
  have hcube : 9 * q ≤ q ^ 3 := by simpa [pow_succ] using Nat.mul_le_mul_right q hsq
  rcases odd_adjacent_two_valuation_one hq ho with hvA | hvB
  · rw [hvA, pow_add]
    norm_num
    have hb : 4 * 2 ^ (q + 1).factorization 2 ≤ 4 * (q + 1) := Nat.mul_le_mul_left 4 hBle
    omega
  · rw [hvB, pow_add, pow_one, Nat.mul_comm 2 _, pow_mul]
    have hb := Nat.pow_le_pow_left hAle 2
    have hsmall : 2 * (q - 1) ^ 2 < q ^ 3 := by
      have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
      have hm := congrArg (fun t : ℕ => t ^ 3) hs
      have hpos : 0 < (q - 1) ^ 3 := pow_pos (by omega) 3
      nlinarith
    nlinarith

/-- Uniform characteristic dominance for linear dimension three, including
both even and odd field sizes and the actual central quotient. -/
theorem linear_three_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.linear 3 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear 3 q)).factorization l < q ^ 3 := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hrespos : residual (.linear 3 q) ≠ 0 := by
    rw [linear_three_residual_factor hq]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by omega)
  have hupper := cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hrespos (dvd_refl _)
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    exact hupper.trans_lt (linear_three_residual_two_contribution_lt hq ho)
  by_cases hl3 : l = 3
  · subst l
    exact hupper.trans_lt (linear_three_residual_three_contribution_lt hq)
  have hdiv := cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq
  rw [linear_three_residual_factor hq] at hdiv
  have hs : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hm : 2 * q ^ 2 ≤ q ^ 3 := by
    calc
      2 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hq
      _ = q ^ 3 := by ring
  have hAless : (q - 1) ^ 2 < q ^ 2 := Nat.pow_lt_pow_left (by omega) (by decide)
  have hCless : q ^ 2 + q + 1 < q ^ 3 := by
    have hdouble : 2 * q ≤ q ^ 2 := by simpa [pow_two, mul_comm] using Nat.mul_le_mul_left q hq
    omega
  rcases linear_three_prime_power_residual hq hl hl2 hl3 hdiv with hA | hB | hC
  · have hb := Nat.le_of_dvd (pow_pos (by omega : 0 < q - 1) 2) hA
    omega
  · have hb := Nat.le_of_dvd (Nat.succ_pos q) hB
    omega
  · exact (Nat.le_of_dvd (Nat.succ_pos (q ^ 2 + q)) hC).trans_lt hCless

end Atlas.OrderArithmetic

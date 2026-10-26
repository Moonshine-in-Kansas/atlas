import Atlas.OrderArithmetic.HigherRankOddDominance
import Mathlib.NumberTheory.Multiplicity

namespace Atlas.OrderArithmetic

/-- The two-adic valuation along the even exponents is an exact LTE block. -/
theorem two_valuation_even_exponent {q i : ℕ} (hq : 2 ≤ q) (ho : Odd q)
    (hi : 1 ≤ i) :
    (q ^ (2 * i) - 1).factorization 2 =
      (q ^ 2 - 1).factorization 2 + i.factorization 2 := by
  have hn : ¬ 2 ∣ q := by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    have := Nat.odd_iff.mp ho
    omega
  have hlarge := padicValNat.pow_two_sub_one (by omega : 1 < q) hn
    (n := 2 * i) (by omega) (even_two_mul i)
  have hsmall := padicValNat.pow_two_sub_one (by omega : 1 < q) hn
    (n := 2) (by decide) (by decide)
  have hlf : (q ^ (2 * i) - 1).factorization 2 + 1 =
      (q + 1).factorization 2 + (q - 1).factorization 2 + (2 * i).factorization 2 := by
    simpa only [Nat.factorization_def _ Nat.prime_two] using hlarge
  have hsf : (q ^ 2 - 1).factorization 2 + 1 =
      (q + 1).factorization 2 + (q - 1).factorization 2 + 1 := by
    simpa only [Nat.factorization_def _ Nat.prime_two, padicValNat_self] using hsmall
  rw [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (by omega),
    Finsupp.add_apply, Nat.prime_two.factorization_self] at hlf
  omega

theorem even_minus_segment_ne_zero {q : ℕ} (hq : 2 ≤ q) (d : ℕ) :
    (∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hh : q ≤ q ^ (2 * i) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 1 ≤ 2 * i)
  omega

/-- Exact accumulated binary valuation of the B/C residual segment. -/
theorem two_valuation_even_segment {q : ℕ} (hq : 2 ≤ q) (ho : Odd q) (d : ℕ) :
    (∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1)).factorization 2 =
      d * (q ^ 2 - 1).factorization 2 + d.factorial.factorization 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hh : q ≤ q ^ (2 * (d + 1)) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 1 ≤ 2 * (d + 1))
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ d + 1),
      Nat.factorization_mul (even_minus_segment_ne_zero hq d) (by omega),
      Finsupp.add_apply, ih, two_valuation_even_exponent hq ho (by omega),
      Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero d),
      Finsupp.add_apply]
    ring

/-- A uniform bound for the binary contribution to the complete even segment. -/
theorem two_contribution_even_segment_le {q : ℕ} (hq : 2 ≤ q) (ho : Odd q) (d : ℕ) :
    2 ^ (∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1)).factorization 2 ≤ q ^ (3 * d) := by
  have hqs : 0 < q ^ 2 - 1 := by
    have hq2 : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hd : 2 ^ (q ^ 2 - 1).factorization 2 ∣ q ^ 2 - 1 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hqs.ne').mpr le_rfl
  have hb := Nat.le_of_dvd hqs hd
  rw [two_valuation_even_segment hq ho, pow_add]
  have hh : 2 ^ (d * (q ^ 2 - 1).factorization 2) =
      (2 ^ (q ^ 2 - 1).factorization 2) ^ d := by rw [← pow_mul, Nat.mul_comm]
  rw [hh]
  calc
    _ ≤ (q ^ 2 - 1) ^ d * 2 ^ d :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hb d) (factorial_prime_contribution_le Nat.prime_two d)
    _ ≤ (q ^ 2) ^ d * q ^ d :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le _ _) d) (Nat.pow_le_pow_left hq d)
    _ = q ^ (3 * d) := by rw [← pow_mul, ← pow_add]; congr 1; omega

/-- Every minus factor divides its even-exponent partner. -/
theorem minus_segment_dvd_even_segment (q d : ℕ) :
    (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)) ∣
      ∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1) := by
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact Nat.pow_sub_one_dvd_pow_sub_one q (dvd_mul_left i 2)

end Atlas.OrderArithmetic

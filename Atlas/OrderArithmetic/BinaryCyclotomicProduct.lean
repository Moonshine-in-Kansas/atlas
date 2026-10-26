import Atlas.OrderArithmetic.BinaryProductBound
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace Atlas.OrderArithmetic
open Polynomial

/-- The normalized binary cyclotomic factors have a telescoping divisor product. -/
theorem binary_cyclotomic_normalized_product {n : ℕ} (hn : 0 < n) :
    (∏ d ∈ n.divisors, (cyclotomic d ℝ).eval 2 / (2 : ℝ) ^ d.totient) =
      1 - (1 / 2 : ℝ) ^ n := by
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Nat.sum_totient]
  have h := congrArg (fun P : ℝ[X] => P.eval 2)
    (prod_cyclotomic_eq_X_pow_sub_one hn ℝ)
  simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at h
  rw [h, div_pow, one_pow]
  field_simp

/-- Multiplicative Möbius inversion gives a finite product for the normalized
binary cyclotomic value. No infinite product or analytic estimate is used. -/
theorem binary_cyclotomic_normalized_moebius {n : ℕ} (hn : 0 < n) :
    (cyclotomic n ℝ).eval 2 / (2 : ℝ) ^ n.totient =
      ∏ d ∈ n.divisors, (1 - (1 / 2 : ℝ) ^ d) ^ ArithmeticFunction.moebius (n / d) := by
  have hf : ∀ n : ℕ, 0 < n →
      (cyclotomic n ℝ).eval 2 / (2 : ℝ) ^ n.totient ≠ 0 := by
    intro n _
    exact div_ne_zero (ne_of_gt (cyclotomic_pos' n (by norm_num))) (by positivity)
  have hg : ∀ n : ℕ, 0 < n → 1 - (1 / 2 : ℝ) ^ n ≠ 0 := by
    intro n hn
    have h : (1 / 2 : ℝ) ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have h := (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero hf hg).mp
    (fun n hn => binary_cyclotomic_normalized_product hn) n hn
  rw [Nat.prod_divisorsAntidiagonal'
    (fun a b => (1 - (1 / 2 : ℝ) ^ b) ^ ArithmeticFunction.moebius a)] at h
  exact h.symm

/-- Dropping Möbius signs only decreases the product of factors in (0,1). -/
theorem binary_factor_le_moebius_power {d : ℕ} (hd : 0 < d) (j : ℕ) :
    1 - (1 / 2 : ℝ) ^ d ≤
      (1 - (1 / 2 : ℝ) ^ d) ^ ArithmeticFunction.moebius j := by
  have ht : (1 / 2 : ℝ) ^ d < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hp : 0 < 1 - (1 / 2 : ℝ) ^ d := by linarith
  have hle : 1 - (1 / 2 : ℝ) ^ d ≤ 1 := by
    have : 0 ≤ (1 / 2 : ℝ) ^ d := by positivity
    linarith
  rcases ArithmeticFunction.moebius_eq_or j with h | h | h
  · simpa [h] using hle
  · simp [h]
  · rw [h, zpow_neg_one, inv_eq_one_div]
    apply (le_div_iff₀ hp).mpr
    nlinarith

/-- A uniform finite-product lower bound for binary cyclotomic values. -/
theorem binary_cyclotomic_quarter_bound {n : ℕ} (hn : 0 < n) :
    (1 / 4 : ℝ) < (cyclotomic n ℝ).eval 2 / (2 : ℝ) ^ n.totient := by
  rw [binary_cyclotomic_normalized_moebius hn]
  have hsubset : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1⟩
  have hfull : (1 / 4 : ℝ) <
      ∏ d ∈ Finset.Icc 1 n, (1 - (1 / 2 : ℝ) ^ d) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    simpa [Nat.add_comm] using binary_product_quarter_lt n
  apply hfull.trans_le
  calc
    (∏ d ∈ Finset.Icc 1 n, (1 - (1 / 2 : ℝ) ^ d)) ≤
        ∏ d ∈ n.divisors, (1 - (1 / 2 : ℝ) ^ d) := by
      apply Finset.prod_le_prod_of_subset_of_le_one hsubset
      · intro d _
        have : (1 / 2 : ℝ) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      · intro d _ _
        have : 0 ≤ (1 / 2 : ℝ) ^ d := by positivity
        linarith
    _ ≤ ∏ d ∈ n.divisors,
        (1 - (1 / 2 : ℝ) ^ d) ^ ArithmeticFunction.moebius (n / d) := by
      apply Finset.prod_le_prod
      · intro d _
        have : (1 / 2 : ℝ) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      · intro d hd
        exact binary_factor_le_moebius_power (Nat.pos_of_mem_divisors hd) _

end Atlas.OrderArithmetic

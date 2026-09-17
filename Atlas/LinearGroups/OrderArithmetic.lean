/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-! # Arithmetic rearrangements of linear-group order formulas -/

namespace Atlas

/-- Factoring the powers out of the ordered-basis count. -/
theorem linear_order_product_factor (q n : ℕ) :
    (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) =
      q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.range n, (q ^ (i + 1) - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ q ^ n - q ^ i) n]
  calc
    (∏ i ∈ Finset.range n, (q ^ n - q ^ i)) =
        ∏ i ∈ Finset.range n, (q ^ i * (q ^ (n - i) - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Nat.mul_sub_left_distrib, ← pow_add, Nat.add_sub_of_le
        (Nat.le_of_lt (Finset.mem_range.mp hi)), mul_one]
    _ = q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.range n, (q ^ (n - i) - 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
    _ = _ := by
      congr 1
      rw [← Finset.prod_range_reflect (fun i ↦ q ^ (i + 1) - 1) n]
      apply Finset.prod_congr rfl
      intro i hi
      congr 2
      have := Finset.mem_range.mp hi
      omega

/-- Separating the scalar factor from the remaining cyclotomic factors. -/
theorem linear_order_product_split (q n : ℕ) (hn : 0 < n) :
    (∏ i ∈ Finset.range n, (q ^ (i + 1) - 1)) =
      (q - 1) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
  rw [← Nat.sub_add_cancel hn, Finset.prod_range_succ']
  simp only [zero_add, pow_one]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  have hlen : n - 1 + 1 + 1 - 2 = n - 1 := by omega
  simp only [hlen]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  omega

end Atlas

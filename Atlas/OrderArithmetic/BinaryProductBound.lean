import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Atlas.OrderArithmetic

/-- A finite geometric-product bound with an explicit positive remainder.
This is the elementary estimate needed for binary cyclotomic values. -/
theorem binary_tail_product_lower (n : ℕ) :
    (1 / 2 : ℝ) + (1 / 2 : ℝ) ^ (n + 1) ≤
      ∏ i ∈ Finset.range n, (1 - (1 / 2 : ℝ) ^ (i + 2)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have ht0 : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
    have ht1 : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
      calc
        (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by ring
    have he : (1 / 2 : ℝ) ^ (n + 2) = (1 / 2 : ℝ) ^ (n + 1) * (1 / 2) := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    rw [Finset.prod_range_succ]
    have hm := mul_le_mul_of_nonneg_right ih
      (show 0 ≤ 1 - (1 / 2 : ℝ) ^ (n + 2) by rw [he]; linarith)
    have hs := mul_nonneg ht0.le (sub_nonneg.mpr ht1)
    rw [show n + 1 + 1 = n + 2 by omega, he]
    rw [he] at hm
    nlinarith

/-- Every finite initial product is bounded strictly away from one quarter. -/
theorem binary_product_quarter_lt (n : ℕ) :
    (1 / 4 : ℝ) < ∏ i ∈ Finset.range n, (1 - (1 / 2 : ℝ) ^ (i + 1)) := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Finset.prod_range_succ']
    have h := binary_tail_product_lower n
    have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
    norm_num only [zero_add, pow_one] at *
    simp only [Nat.add_assoc] at *
    nlinarith

end Atlas.OrderArithmetic

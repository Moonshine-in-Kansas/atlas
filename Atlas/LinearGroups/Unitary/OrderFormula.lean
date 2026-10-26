import Atlas.LinearGroups.Unitary.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! # Arithmetic of the unitary order products

These are numerical expressions only. Their identification with cardinalities of
actual matrix groups is a separate geometric theorem.
-/
namespace Atlas.Unitary
open Finset

/-- The full unitary order expression, indexed from matrix dimension zero. -/
def orderU (q n : ℕ) : ℕ :=
  q ^ (∑ i ∈ range n, i) * ∏ i ∈ range n, orderFactor q (i + 1)

/-- The special unitary order expression; the determinant factor is omitted. -/
def orderSU (q n : ℕ) : ℕ :=
  q ^ (∑ i ∈ range n, i) * ∏ i ∈ range (n - 1), orderFactor q (i + 2)

@[simp] theorem orderFactor_one (q : ℕ) : orderFactor q 1 = q + 1 := by
  simp [orderFactor]

@[simp] theorem orderU_zero (q : ℕ) : orderU q 0 = 1 := by simp [orderU]
@[simp] theorem orderSU_zero (q : ℕ) : orderSU q 0 = 1 := by simp [orderSU]
@[simp] theorem orderSU_one (q : ℕ) : orderSU q 1 = 1 := by simp [orderSU]

/-- The recurrence furnished by counting norm-one vectors. -/
theorem orderU_succ (q n : ℕ) :
    orderU q (n + 1) = q ^ n * orderFactor q (n + 1) * orderU q n := by
  simp only [orderU, sum_range_succ, prod_range_succ, pow_add]
  ring

/-- Removing the dimension-one factor exactly removes the determinant image. -/
theorem orderU_eq_mul_orderSU (q n : ℕ) (hn : 0 < n) :
    orderU q n = (q + 1) * orderSU q n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [orderU, orderSU, Nat.succ_sub_one]
  rw [prod_range_succ']
  simp only [zero_add, orderFactor_one]
  ring

/-- The exponent is the usual number of positive type-A roots. -/
theorem orderU_formula (q n : ℕ) :
    orderU q n = q ^ (n * (n - 1) / 2) *
      ∏ i ∈ range n, orderFactor q (i + 1) := by
  rw [orderU, sum_range_id]

theorem orderSU_formula (q n : ℕ) :
    orderSU q n = q ^ (n * (n - 1) / 2) *
      ∏ i ∈ range (n - 1), orderFactor q (i + 2) := by
  rw [orderSU, sum_range_id]

theorem orderU_div_det (q n : ℕ) (hn : 0 < n) :
    orderU q n / (q + 1) = orderSU q n := by
  rw [orderU_eq_mul_orderSU q n hn, Nat.mul_div_right _ (by omega)]

theorem determinant_factor_dvd_orderU (q n : ℕ) (hn : 0 < n) :
    q + 1 ∣ orderU q n := ⟨orderSU q n, orderU_eq_mul_orderSU q n hn⟩

/-- The conventional product with indices from one through the dimension. -/
theorem orderU_formula_Icc (q n : ℕ) :
    orderU q n = q ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, orderFactor q i := by
  rw [orderU_formula, ← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  simp [Nat.add_comm]

/-- The conventional special-unitary product with indices from two onwards. -/
theorem orderSU_formula_Icc (q n : ℕ) :
    orderSU q n = q ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 2 n, orderFactor q i := by
  rw [orderSU_formula, ← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  have h : n + 1 - 2 = n - 1 := by omega
  simp [h, Nat.add_comm]

/-- The exact exponent step needed for the conventional order induction. -/
theorem order_exponent_succ (n : ℕ) :
    (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  simpa only [sum_range_id, Nat.add_sub_cancel] using
    (Finset.sum_range_succ (fun i : ℕ => i) n)

end Atlas.Unitary


import Atlas.Algebra.FiniteFieldSignSquares
import Mathlib.FieldTheory.Finite.Basic

/-! # Nondegenerate diagonal binary forms represent every finite odd-field value -/
noncomputable section
namespace Atlas
open Polynomial
variable {F : Type*} [Field F] [Finite F]

/-- The square-value counting argument works over every finite odd field, not just prime fields. -/
theorem finite_field_binary_represents (h2 : (2 : F) ≠ 0) (a b : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (c : F) : ∃ x y : F, a * x ^ 2 + b * y ^ 2 = c := by
  letI := Fintype.ofFinite F
  have hf : degree (C a * X ^ 2 : F[X]) = 2 := degree_C_mul_X_pow 2 ha
  have hg : degree (C b * X ^ 2 - C c : F[X]) = 2 := by
    have hlt : degree (C c : F[X]) < degree (C b * X ^ 2 : F[X]) := by
      rw [degree_C_mul_X_pow 2 hb]
      exact lt_of_le_of_lt degree_C_le (by decide)
    rw [degree_sub_eq_left_of_degree_lt hlt]
    exact degree_C_mul_X_pow 2 hb
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (by simpa only [Nat.card_eq_fintype_card] using odd_card_mod_two h2)
  refine ⟨x, y, ?_⟩
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub] at h
  linear_combination h

/-- In particular every value, hence every nonzero value, is a sum of two squares. -/
theorem finite_field_sum_two_squares (h2 : (2 : F) ≠ 0) (c : F) :
    ∃ x y : F, x ^ 2 + y ^ 2 = c := by
  simpa only [one_mul] using finite_field_binary_represents h2 1 1 one_ne_zero one_ne_zero c
end Atlas

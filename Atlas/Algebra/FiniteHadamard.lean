import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-! Finite conjugation by a nilpotent exponential when the second adjoint
commutator vanishes. Only the conjugating operator is assumed nilpotent. -/

noncomputable section
namespace Atlas.Algebra

variable {S : Type*} [Ring S] [Algebra ℚ S]

private theorem pow_succ_mul_of_central_bracket
    (A B C : S) (hAB : A * B = B * A + C) (hAC : Commute A C) (n : ℕ) :
    A ^ (n + 1) * B = B * A ^ (n + 1) +
      ((n + 1 : ℕ) : ℚ) • (C * A ^ n) := by
  induction n with
  | zero =>
      simpa only [Nat.zero_add, Nat.cast_one, pow_one, pow_zero,
        mul_one, one_smul] using hAB
  | succ n ih =>
      calc
        A ^ (n + 1 + 1) * B = A * (A ^ (n + 1) * B) := by
          rw [pow_succ', mul_assoc]
        _ = A * (B * A ^ (n + 1) +
              ((n + 1 : ℕ) : ℚ) • (C * A ^ n)) := by rw [ih]
        _ = (B * A + C) * A ^ (n + 1) +
              ((n + 1 : ℕ) : ℚ) • (C * A ^ (n + 1)) := by
          rw [mul_add, ← mul_assoc A B, hAB, mul_smul_comm]
          congr 1
          rw [← mul_assoc A C, hAC.eq, mul_assoc, ← pow_succ']
        _ = B * A ^ (n + 1 + 1) +
              ((n + 1 + 1 : ℕ) : ℚ) • (C * A ^ (n + 1)) := by
          rw [add_mul, mul_assoc, ← pow_succ']
          simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
          abel

private theorem inverse_factorial_succ_mul (n : ℕ) :
    (((n + 1).factorial : ℚ)⁻¹) * ((n + 1 : ℕ) : ℚ) =
      (n.factorial : ℚ)⁻¹ := by
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hn, mul_one]

/-- The length-two finite Hadamard identity. No nilpotence assumption on B
or on its commutator with A occurs. -/
theorem exp_mul_eq_add_bracket_mul_exp
    (A B : S) (hA : IsNilpotent A) (hAC : Commute A (A * B - B * A)) :
    IsNilpotent.exp A * B = (B + (A * B - B * A)) * IsNilpotent.exp A := by
  let C := A * B - B * A
  have hAB : A * B = B * A + C := by
    dsimp only [C]
    abel
  have hAC' : Commute A C := hAC
  let f : ℕ → S := fun k => (k.factorial : ℚ)⁻¹ • A ^ k
  have hf0 : f 0 = 1 := by simp [f]
  have hterm (k : ℕ) : f (k + 1) * B - B * f (k + 1) = C * f k := by
    calc
      f (k + 1) * B - B * f (k + 1) =
          ((k + 1).factorial : ℚ)⁻¹ •
            (A ^ (k + 1) * B - B * A ^ (k + 1)) := by
        simp only [f, smul_sub, smul_mul_assoc, mul_smul_comm]
      _ = ((k + 1).factorial : ℚ)⁻¹ •
          (((k + 1 : ℕ) : ℚ) • (C * A ^ k)) := by
        rw [pow_succ_mul_of_central_bracket A B C hAB hAC', add_sub_cancel_left]
      _ = (k.factorial : ℚ)⁻¹ • (C * A ^ k) := by
        rw [smul_smul, inverse_factorial_succ_mul]
      _ = C * f k := by dsimp only [f]; rw [mul_smul_comm]
  obtain ⟨N, hN⟩ := hA
  have hN1 : A ^ (N + 1) = 0 := by rw [pow_succ, hN, zero_mul]
  have hexpN : IsNilpotent.exp A = ∑ k ∈ Finset.range N, f k :=
    IsNilpotent.exp_eq_sum hN
  have hexpN1 : IsNilpotent.exp A = ∑ k ∈ Finset.range (N + 1), f k :=
    IsNilpotent.exp_eq_sum hN1
  have hsum : (∑ k ∈ Finset.range (N + 1), (f k * B - B * f k)) =
      C * ∑ k ∈ Finset.range N, f k := by
    rw [Finset.sum_range_succ']
    simp only [hterm, hf0, one_mul, mul_one, sub_self, add_zero, Finset.mul_sum]
  have hcomm : IsNilpotent.exp A * B - B * IsNilpotent.exp A =
      C * IsNilpotent.exp A := by
    calc
      IsNilpotent.exp A * B - B * IsNilpotent.exp A =
          ∑ k ∈ Finset.range (N + 1), (f k * B - B * f k) := by
        simp only [hexpN1, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
      _ = C * ∑ k ∈ Finset.range N, f k := hsum
      _ = C * IsNilpotent.exp A := by rw [← hexpN]
  calc
    IsNilpotent.exp A * B = C * IsNilpotent.exp A + B * IsNilpotent.exp A :=
      sub_eq_iff_eq_add.mp hcomm
    _ = (B + (A * B - B * A)) * IsNilpotent.exp A := by
      change C * IsNilpotent.exp A + B * IsNilpotent.exp A =
        (B + C) * IsNilpotent.exp A
      rw [add_mul, add_comm]

/-- Actual finite exponential conjugation, with inverse exp(−A). -/
theorem exp_mul_mul_exp_neg_eq_add_bracket
    (A B : S) (hA : IsNilpotent A) (hAC : Commute A (A * B - B * A)) :
    IsNilpotent.exp A * B * IsNilpotent.exp (-A) = B + (A * B - B * A) := by
  rw [exp_mul_eq_add_bracket_mul_exp A B hA hAC, mul_assoc,
    IsNilpotent.exp_mul_exp_neg_self hA, mul_one]

end Atlas.Algebra

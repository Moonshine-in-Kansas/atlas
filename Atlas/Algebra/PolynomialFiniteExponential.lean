import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-! Source candidate: finite nilpotent exponential differentiation with
noncommutative coefficients. No analytic exponential or BCH theorem. -/

noncomputable section
namespace Atlas.Algebra
open Polynomial

variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- Finite exponentials preserve commutation with a fixed element. This
uses the actual finite-sum definition and does not require nilpotence. -/
theorem commute_finiteExp_right {a b : S} (h : Commute a b) :
    Commute a (IsNilpotent.exp b) := by
  rw [IsNilpotent.exp]
  exact Commute.sum_right _ _ _ fun k _ => (h.pow_right k).smul_right _

/-- Power differentiation for possibly noncommutative coefficients, with
the required commutation hypothesis explicit. -/
theorem polynomial_derivative_pow_succ_of_commute
    {p : S[X]} (hp : Commute p p.derivative) (n : ℕ) :
    (p ^ (n + 1)).derivative = ((n + 1 : ℕ) : ℚ) • (p ^ n * p.derivative) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmove : (p ^ n * p.derivative) * p = p ^ (n + 1) * p.derivative := by
      rw [mul_assoc, hp.symm.eq, ← mul_assoc, ← pow_succ]
    calc
      (p ^ (n + 1 + 1)).derivative =
          (p ^ (n + 1)).derivative * p + p ^ (n + 1) * p.derivative := by
        rw [pow_succ, derivative_mul]
      _ = ((n + 1 : ℕ) : ℚ) • ((p ^ n * p.derivative) * p) +
          p ^ (n + 1) * p.derivative := by rw [ih, smul_mul_assoc]
      _ = ((n + 1 + 1 : ℕ) : ℚ) • (p ^ (n + 1) * p.derivative) := by
        rw [hmove]
        simp only [Nat.cast_add, Nat.cast_one]
        module

/-- Formal differentiation of a finite nilpotent exponential over a
noncommutative rational algebra. Nilpotence and self-derivative commutation
are both explicit; no statement is made for a general polynomial. -/
theorem polynomial_derivative_exp_of_commute
    {p : S[X]} (hnil : IsNilpotent p) (hp : Commute p p.derivative) :
    (IsNilpotent.exp p).derivative = IsNilpotent.exp p * p.derivative := by
  obtain ⟨n, hn⟩ := hnil
  have hn1 : p ^ (n + 1) = 0 := pow_eq_zero_of_le (Nat.le_succ n) hn
  calc
    (IsNilpotent.exp p).derivative =
        ∑ k ∈ Finset.range (n + 1),
          (k.factorial : ℚ)⁻¹ • (p ^ k).derivative := by
      rw [IsNilpotent.exp_eq_sum hn1, derivative_sum]
      simp only [derivative_smul]
    _ = ∑ k ∈ Finset.range n,
        ((k + 1).factorial : ℚ)⁻¹ • (p ^ (k + 1)).derivative := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, derivative_one, smul_zero, add_zero]
    _ = ∑ k ∈ Finset.range n,
        (k.factorial : ℚ)⁻¹ • (p ^ k * p.derivative) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [polynomial_derivative_pow_succ_of_commute hp, smul_smul]
      congr 1
      have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp
    _ = IsNilpotent.exp p * p.derivative := by
      rw [IsNilpotent.exp_eq_sum hn, Finset.sum_mul]
      simp only [smul_mul_assoc]

/-- Equality of derivatives and constant coefficients determines a
polynomial over any (possibly noncommutative) rational algebra. -/
theorem polynomial_eq_of_derivative_eq_of_coeff_zero_eq
    (p q : S[X]) (hd : p.derivative = q.derivative)
    (hzero : p.coeff 0 = q.coeff 0) : p = q := by
  letI : IsAddTorsionFree S := IsAddTorsionFree.of_module_rat S
  have hdiff : (p - q).derivative = 0 := by rw [derivative_sub, hd, sub_self]
  have hconst := Polynomial.eq_C_of_derivative_eq_zero hdiff
  have hz : (p - q).coeff 0 = 0 := by simp only [coeff_sub, hzero, sub_self]
  rw [hz, C_0] at hconst
  exact sub_eq_zero.mp hconst

end Atlas.Algebra

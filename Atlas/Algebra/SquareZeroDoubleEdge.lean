import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-! A denominator-free double-edge word identity for actual square-zero
operators. The hypotheses are literal multiplication identities. -/

namespace Atlas.Algebra

private theorem squareZero_doubleEdge_unscaled {A : Type*} [Ring A]
    (a b : A) (haa : a * a = 0) (hbb : b * b = 0) (hbab : b * a * b = 0) :
    (1 + a) * (1 + b) * (1 - a) * (1 - b) =
      1 + (a * b - b * a) - a * b * a := by
  calc
    _ = 1 + (a * b - b * a) - a * b * a - (a * a) - (b * b) -
        a * (b * b) + (a * a) * b + (b * a * b) + a * (b * a * b) := by
      noncomm_ring
    _ = _ := by simp only [haa, hbb, hbab, mul_zero, zero_mul, sub_zero, add_zero]

/-- The factorized mixed double-edge word. No division, characteristic
restriction, bracket nilpotence or nonvanishing premise occurs. -/
theorem squareZero_doubleEdge_commutator_factors
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (a b : A) (haa : a * a = 0) (hbb : b * b = 0) (hbab : b * a * b = 0)
    (s t : R) :
    (1 + s • a) * (1 + t • b) * (1 + (-s) • a) * (1 + (-t) • b) =
      (1 + (s * t) • (a * b - b * a)) * (1 + (s ^ 2 * t) • (-(a * b * a))) := by
  have hsa : (s • a) * (s • a) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, haa, smul_zero]
  have htb : (t • b) * (t • b) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hbb, smul_zero]
  have hscaledBAB : (t • b) * (s • a) * (t • b) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hbab, smul_zero]
  have hscaledC : (s • a) * (t • b) - (t • b) * (s • a) =
      (s * t) • (a * b - b * a) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm t s, smul_sub]
  have hscaledABA : (s • a) * (t • b) * (s • a) =
      (s ^ 2 * t) • (a * b * a) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
  have hzero : (a * b - b * a) * (a * b * a) = 0 := by
    calc
      _ = a * (b * a * b) * a - b * (a * a) * b * a := by noncomm_ring
      _ = 0 := by simp only [hbab, haa, mul_zero, zero_mul, sub_self]
  calc
    _ = 1 + ((s • a) * (t • b) - (t • b) * (s • a)) -
        (s • a) * (t • b) * (s • a) := by
      simpa only [neg_smul, sub_eq_add_neg] using
        squareZero_doubleEdge_unscaled (s • a) (t • b) hsa htb hscaledBAB
    _ = 1 + (s * t) • (a * b - b * a) - (s ^ 2 * t) • (a * b * a) := by
      rw [hscaledC, hscaledABA]
    _ = _ := by
      simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
        mul_smul_comm, smul_neg, mul_neg, hzero, smul_zero, neg_zero, add_zero]
      module

end Atlas.Algebra

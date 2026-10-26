import Atlas.OrderArithmetic.Positivity
import Atlas.OrderArithmetic.AlternatingBounds
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Atlas.OrderArithmetic

/-- Elementary exponential bound, with no logarithms. -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have := Nat.one_le_pow n 2 (by omega)
    omega

/-- Legendre's formula gives the precise inequality needed for the cutoff. -/
theorem factorial_valuation_bound {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (p - 1) * n.factorial.factorization p ≤ n := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, sub_one_mul_padicValNat_factorial n]
  exact Nat.sub_le _ _

/-- Every prime-power contribution to n! is at most 2^n. -/
theorem factorial_prime_contribution_le {p : ℕ} (hp : p.Prime) (n : ℕ) :
    p ^ n.factorial.factorization p ≤ 2 ^ n := by
  have hpbound : p ≤ 2 ^ (p - 1) := by
    have := succ_le_two_pow (p - 1)
    have := hp.two_le
    omega
  calc
    p ^ n.factorial.factorization p ≤ (2 ^ (p - 1)) ^ n.factorial.factorization p :=
      Nat.pow_le_pow_left hpbound _
    _ = 2 ^ ((p - 1) * n.factorial.factorization p) := by rw [pow_mul]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (factorial_valuation_bound hp n)

/-- This part of alternating/Lie reduction is unconditional: the characteristic
contribution of an equal Lie order is bounded by 2^n. -/
theorem characteristic_power_le_of_alternating_eq {x : RawEntry} {n : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hn : 5 ≤ n)
    (h : order x = order (.alternating n)) :
    fieldSize x ^ characteristicExponent x ≤ 2 ^ n := by
  obtain ⟨p, f, hp, hf, hq⟩ := lie_field_primePower hx hl
  have hv := order_characteristic_valuation hx hl hp hf hq
  have hdiv : 2 ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
  have hvle : (order x).factorization p ≤ n.factorial.factorization p := by
    rw [h]
    change (n.factorial / 2).factorization p ≤ n.factorial.factorization p
    rw [Nat.factorization_div hdiv]
    exact Nat.sub_le _ _
  rw [hq, ← pow_mul]
  exact (Nat.pow_le_pow_right hp.pos (by omega : f * characteristicExponent x ≤
    n.factorial.factorization p)).trans (factorial_prime_contribution_le hp n)

/-- The growth estimate is an explicit remaining input here, not an implicit
assumption of the final classification. -/
theorem alternating_degree_lt_twenty_of_growth {x : RawEntry} {n : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hn : 5 ≤ n)
    (h : order x = order (.alternating n))
    (hgrowth : order x < fieldSize x ^ (3 * characteristicExponent x)) : n < 20 := by
  have hq := characteristic_power_le_of_alternating_eq hx hl hn h
  have hbound : fieldSize x ^ (3 * characteristicExponent x) ≤ 8 ^ n := by
    calc
      fieldSize x ^ (3 * characteristicExponent x) =
          (fieldSize x ^ characteristicExponent x) ^ 3 := by rw [← pow_mul, mul_comm 3]
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq _
      _ = 8 ^ n := by rw [← pow_mul, mul_comm n, pow_mul]; norm_num
  apply alternating_degree_lt_twenty
  change order (.alternating n) < 8 ^ n
  rw [← h]
  exact hgrowth.trans_le hbound

end Atlas.OrderArithmetic

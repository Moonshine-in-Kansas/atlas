import Atlas.OrderArithmetic.Parameters
import Atlas.OrderArithmetic.Orders
import Atlas.OrderArithmetic.ValuationCore
import Mathlib.NumberTheory.Fermat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Atlas.OrderArithmetic

/-- The exponent of a prime Mersenne number is prime.  This uses the general
divisibility argument for prime numbers of the form `a ^ n - 1`. -/
theorem mersenne_exponent_prime {k : ℕ} (hp : (2 ^ k - 1).Prime) : k.Prime := by
  apply (Nat.prime_of_pow_sub_one_prime (a := 2) ?_ hp).2
  intro hk
  subst k
  norm_num at hp

/-- The excluded linear degree-two field of size three removes exponent two. -/
theorem mersenne_exponent_three_le {k : ℕ} (hp : (2 ^ k - 1).Prime)
    (hx : Admissible (.linear 2 (2 ^ k - 1))) : 3 ≤ k := by
  have hk := (mersenne_exponent_prime hp).two_le
  by_contra h
  have he : k = 2 := by omega
  subst k
  norm_num [Admissible] at hx

/-- Every admissible Mersenne exponent is odd; no finite list of primes is used. -/
theorem mersenne_exponent_odd {k : ℕ} (hp : (2 ^ k - 1).Prime)
    (hx : Admissible (.linear 2 (2 ^ k - 1))) : Odd k := by
  exact (mersenne_exponent_prime hp).odd_of_ne_two
    (by have := mersenne_exponent_three_le hp hx; omega)

/-- The elementary prime-product split used after identifying a characteristic
contribution.  It makes no assumption that such a contribution is dominant. -/
theorem mersenne_prime_product_split {k f a : ℕ} (hp : (2 ^ k - 1).Prime)
    (h : f * a = k) : (a = 1 ∧ f = k) ∨ (f = 1 ∧ a = k) := by
  have hk := mersenne_exponent_prime hp
  have had : a ∣ k := by rw [← h]; exact dvd_mul_left a f
  rcases hk.eq_one_or_self_of_dvd a had with ha | ha
  · left
    exact ⟨ha, by simpa [ha] using h⟩
  · right
    refine ⟨?_, ha⟩
    rw [ha] at h
    have hh : f * k = 1 * k := by simpa using h
    exact Nat.eq_of_mul_eq_mul_right hk.pos hh

/-- Mersenne parameters are determined by their characteristic-two contribution. -/
theorem mersenne_parameter_unique {k l : ℕ} (h : 2 ^ k = 2 ^ l) :
    k = l ∧ 2 ^ k - 1 = 2 ^ l - 1 := by
  exact ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) h, congrArg (fun n : ℕ => n - 1) h⟩

/-- The successor of a Mersenne parameter is exactly the indicated power of two. -/
theorem mersenne_successor (k : ℕ) : (2 ^ k - 1) + 1 = 2 ^ k := by
  exact Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))

/-- An exact factorization of the degree-two order formula, valid even before
requiring the Mersenne parameter to be prime. -/
theorem mersenne_linear_two_order {k : ℕ} (hk : 3 ≤ k) :
    order (.linear 2 (2 ^ k - 1)) =
      2 ^ k * ((2 ^ k - 1) * (2 ^ (k - 1) - 1)) := by
  let t := 2 ^ (k - 1)
  let p := 2 ^ k - 1
  have ht : 2 ≤ t := Nat.le_pow (by omega)
  have ht1 : t - 1 + 1 = t := Nat.sub_add_cancel (by omega)
  have hpow : 2 ^ k = 2 * t := by
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
      _ = 2 * t := by rw [pow_succ']
  have hp1 : p + 1 = 2 * t := by
    simpa only [p, hpow] using mersenne_successor k
  have hp : 2 ≤ p := by omega
  have hpred : p - 1 = 2 * (t - 1) := by omega
  have hgcd : Nat.gcd 2 (p - 1) = 2 :=
    Nat.gcd_eq_left ⟨t - 1, hpred⟩
  have hsq : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsq1 : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel hsq
  have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have hp0 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    nlinarith
  have hproduct : p * (p ^ 2 - 1) =
      (2 ^ k * (p * (t - 1))) * 2 := by
    rw [hfactor, hpred, hp1, hpow]
    ring
  change order (.linear 2 p) = 2 ^ k * (p * (t - 1))
  have ho : order (.linear 2 p) = p * (p ^ 2 - 1) / Nat.gcd 2 (p - 1) := by
    simp [order, numerator, fieldSize, characteristicExponent, residual, denominator]
  rw [ho, hgcd, hproduct, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- Exact two-adic valuation in the infinite Mersenne branch.  Primality of
`2 ^ k - 1` is unnecessary for this identity of numerical formulas. -/
theorem mersenne_linear_two_valuation {k : ℕ} (hk : 3 ≤ k) :
    (order (.linear 2 (2 ^ k - 1))).factorization 2 = k := by
  have hp : Nat.Prime 2 := by decide
  have hleft : ¬ 2 ∣ 2 ^ k - 1 :=
    prime_not_dvd_pow_sub_one hp (by decide) dvd_rfl (by omega)
  have hright : ¬ 2 ∣ 2 ^ (k - 1) - 1 :=
    prime_not_dvd_pow_sub_one hp (by decide) dvd_rfl (by omega)
  have hres : ¬ 2 ∣ (2 ^ k - 1) * (2 ^ (k - 1) - 1) :=
    hp.prime.not_dvd_mul hleft hright
  have hn : (2 ^ k - 1) * (2 ^ (k - 1) - 1) ≠ 0 := by
    intro he
    exact hres (he ▸ dvd_zero 2)
  rw [mersenne_linear_two_order hk,
    Nat.factorization_mul (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) hn]
  simp only [Finsupp.add_apply, Nat.factorization_pow_self hp,
    Nat.factorization_eq_zero_of_not_dvd hres, add_zero]

end Atlas.OrderArithmetic

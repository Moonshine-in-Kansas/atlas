import Atlas.OrderArithmetic.CyclotomicPrimeSupport
import Mathlib.Algebra.Ring.Parity

namespace Atlas.OrderArithmetic
open Polynomial

/-- The literal value of a two-power cyclotomic polynomial at a natural base. -/
theorem cyclotomic_two_power_eval_natAbs {a k : ℕ} (hk : 1 ≤ k) :
    ((cyclotomic (2 ^ k) ℤ).eval (a : ℤ)).natAbs = a ^ (2 ^ (k - 1)) + 1 := by
  have hg := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := k - 1)
    (by decide : Nat.Prime 2)
  rw [show k - 1 + 1 = k by omega] at hg
  have hpoly : cyclotomic (2 ^ k) ℤ = X ^ (2 ^ (k - 1)) + 1 := by
    simpa [Finset.sum_range_succ, add_comm] using hg
  rw [hpoly]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  have hc : (a : ℤ) ^ (2 ^ (k - 1)) + 1 = ((a ^ (2 ^ (k - 1)) + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  rw [hc, Int.natAbs_natCast]

/-- At an odd base and index at least four, the cyclotomic value is two modulo four. -/
theorem cyclotomic_two_power_eval_mod_four {a k : ℕ} (ha : Odd a) (hk : 2 ≤ k) :
    ((cyclotomic (2 ^ k) ℤ).eval (a : ℤ)).natAbs % 4 = 2 := by
  rw [cyclotomic_two_power_eval_natAbs (by omega)]
  have hexp : 2 ^ (k - 1) = 2 ^ (k - 2) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hodd : Odd (a ^ (2 ^ (k - 2))) := ha.pow
  have hb2 := Nat.odd_iff.mp hodd
  have hb4 := Nat.mod_lt (a ^ (2 ^ (k - 2))) (by decide : 0 < 4)
  have hcases : a ^ (2 ^ (k - 2)) % 4 = 1 ∨ a ^ (2 ^ (k - 2)) % 4 = 3 := by omega
  have hsq : (a ^ (2 ^ (k - 2))) ^ 2 % 4 = 1 := by
    rw [Nat.pow_mod]
    rcases hcases with h | h <;> norm_num [h]
  rw [hexp, pow_mul, Nat.add_mod, hsq]

/-- Divisibility by two, but not by four, for the binary bad-prime branch. -/
theorem cyclotomic_two_power_exact_two_divisibility {a k : ℕ}
    (ha : Odd a) (hk : 2 ≤ k) :
    2 ∣ ((cyclotomic (2 ^ k) ℤ).eval (a : ℤ)).natAbs ∧
    ¬ 4 ∣ ((cyclotomic (2 ^ k) ℤ).eval (a : ℤ)).natAbs := by
  have hm := cyclotomic_two_power_eval_mod_four ha hk
  constructor
  · exact Nat.dvd_of_mod_eq_zero (by omega)
  · intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega

/-- Exact two-adic valuation one. This proves only the two-power index branch,
not the general odd-prime cyclotomic valuation statement. -/
theorem cyclotomic_two_power_factorization_two {a k : ℕ} (ha : Odd a) (hk : 2 ≤ k) :
    (((cyclotomic (2 ^ k) ℤ).eval (a : ℤ)).natAbs).factorization 2 = 1 := by
  let N := ((cyclotomic (2 ^ k) ℤ).eval (a : ℤ)).natAbs
  have hm : N % 4 = 2 := cyclotomic_two_power_eval_mod_four ha hk
  have hn : N ≠ 0 := by omega
  obtain ⟨hdiv, hnot⟩ := cyclotomic_two_power_exact_two_divisibility ha hk
  have hp : Nat.Prime 2 := by decide
  have hlow : 1 ≤ N.factorization 2 :=
    (hp.dvd_iff_one_le_factorization hn).mp hdiv
  have hupp : ¬ 2 ≤ N.factorization 2 := by
    intro htwo
    have hd : 2 ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization hn).mpr htwo
    exact hnot (by simpa using hd)
  change N.factorization 2 = 1
  omega

end Atlas.OrderArithmetic

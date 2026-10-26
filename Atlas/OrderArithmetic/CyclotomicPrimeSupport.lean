import Atlas.OrderArithmetic.CyclotomicBadPrime
import Mathlib.Data.Nat.Factorization.Basic

namespace Atlas.OrderArithmetic
open Polynomial

/-- Every prime factor of a cyclotomic value dominates the prime factors of its
index, after removing its own prime-power part from that index. -/
theorem cyclotomic_prime_factor_dominates_index_primes {a n l r : ℕ}
    (hn : 0 < n) (hl : l.Prime)
    (hdiv : l ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs)
    (hr : r.Prime) (hrdiv : r ∣ n) : r ≤ l := by
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) l hl.ne_one
  rw [hnm] at hdiv hrdiv
  exact cyclotomic_prime_power_index_prime_bound hl hm hdiv hr hrdiv

/-- Any prime factor which is not primitive must divide the cyclotomic index. -/
theorem cyclotomic_nonprimitive_prime_factor_dvd_index {a n l : ℕ}
    (ha : 2 ≤ a) (hn : 0 < n) (hl : l.Prime)
    (hdiv : l ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs)
    (hnon : ¬ PrimitiveDivisor a n l) : l ∣ n := by
  by_contra hind
  exact hnon (cyclotomic_prime_factor_primitive_of_not_dvd_index ha hn hl hdiv hind)

/-- A nonprimitive prime factor is the largest prime factor of the index,
expressed intrinsically without choosing a maximum-prime-factor function. -/
theorem cyclotomic_nonprimitive_prime_factor_is_largest {a n l : ℕ}
    (ha : 2 ≤ a) (hn : 0 < n) (hl : l.Prime)
    (hdiv : l ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs)
    (hnon : ¬ PrimitiveDivisor a n l) :
    l ∣ n ∧ ∀ r : ℕ, r.Prime → r ∣ n → r ≤ l := by
  refine ⟨cyclotomic_nonprimitive_prime_factor_dvd_index ha hn hl hdiv hnon, ?_⟩
  intro r hr hrdiv
  exact cyclotomic_prime_factor_dominates_index_primes hn hl hdiv hr hrdiv

/-- In the absence of a primitive divisor, all prime factors of the cyclotomic
value coincide. This does not yet determine their valuation. -/
theorem cyclotomic_prime_factors_eq_of_no_primitive {a n l r : ℕ}
    (ha : 2 ≤ a) (hn : 0 < n) (hno : ¬ ∃ s : ℕ, PrimitiveDivisor a n s)
    (hl : l.Prime) (hr : r.Prime)
    (hdivl : l ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs)
    (hdivr : r ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs) : l = r := by
  have hln : l ∣ n := cyclotomic_nonprimitive_prime_factor_dvd_index ha hn hl hdivl
    (fun h => hno ⟨l, h⟩)
  have hrn : r ∣ n := cyclotomic_nonprimitive_prime_factor_dvd_index ha hn hr hdivr
    (fun h => hno ⟨r, h⟩)
  exact Nat.le_antisymm
    (cyclotomic_prime_factor_dominates_index_primes hn hr hdivr hl hln)
    (cyclotomic_prime_factor_dominates_index_primes hn hl hdivl hr hrn)

end Atlas.OrderArithmetic

import Atlas.OrderArithmetic.FactorialValuation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

namespace Atlas.OrderArithmetic
open Polynomial

/-- For bases at least three, an evaluated cyclotomic polynomial exceeds every
prime factor of its index. Together with the exact bad-prime valuation, this is
the size contradiction needed for primitive-divisor existence. -/
theorem index_prime_lt_cyclotomic_value {a n l : ℕ}
    (ha : 3 ≤ a) (hn : 1 < n) (hl : l.Prime) (hln : l ∣ n) :
    l < ((cyclotomic n ℤ).eval (a : ℤ)).natAbs := by
  have htot : l - 1 ∣ n.totient := by
    simpa only [Nat.totient_prime hl] using Nat.totient_dvd_of_dvd hln
  have ht := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega : 0 < n)) htot
  have hl1 : 1 ≤ l := hl.one_lt.le
  calc
    l = (l - 1) + 1 := by omega
    _ ≤ 2 ^ (l - 1) := succ_le_two_pow _
    _ ≤ 2 ^ n.totient := Nat.pow_le_pow_right (by omega) ht
    _ ≤ (a - 1) ^ n.totient := Nat.pow_le_pow_left (by omega) _
    _ < ((cyclotomic n ℤ).eval (a : ℤ)).natAbs :=
      sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn (by omega)

end Atlas.OrderArithmetic

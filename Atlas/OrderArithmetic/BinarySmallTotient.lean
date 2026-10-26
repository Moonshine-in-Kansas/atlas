import Atlas.OrderArithmetic.FactorialValuation
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.IntervalCases

namespace Atlas.OrderArithmetic

/-- Beyond seven, the elementary exponential bound dominates four times the index. -/
theorem four_mul_lt_two_pow_pred {k : ℕ} (hk : 7 ≤ k) : 4 * k < 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hpred : k + 1 - 1 = k := by omega
    rw [hpred, hpow]
    nlinarith

/-- The finite binary remainder follows from the totient bound and the largest
prime factor, without imposing an arbitrary cutoff on the index. -/
theorem binary_small_totient_indices {n l : ℕ} (hn : 2 < n) (hl : l.Prime)
    (hln : l ∣ n) (hmax : ∀ r : ℕ, r.Prime → r ∣ n → r ≤ l)
    (hsize : 2 ^ n.totient < 4 * l) :
    n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 10 := by
  have htotpos : 0 < n.totient := Nat.totient_pos.mpr (by omega)
  have htotdiv : l - 1 ∣ n.totient := by
    simpa only [Nat.totient_prime hl] using Nat.totient_dvd_of_dvd hln
  have htotle : l - 1 ≤ n.totient := Nat.le_of_dvd htotpos htotdiv
  have hlsmall : l < 7 := by
    by_contra h
    have hlarge := four_mul_lt_two_pow_pred (by omega : 7 ≤ l)
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) htotle
    omega
  have hlcases : l = 2 ∨ l = 3 ∨ l = 5 := by
    have hl2 := hl.two_le
    interval_cases l <;> norm_num at hl <;> omega
  have heven := Nat.totient_even hn
  rcases hlcases with rfl | rfl | rfl
  · have hphi_lt : n.totient < 3 := by
      by_contra h
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ n.totient by omega)
      norm_num at hh
      omega
    have hphi : n.totient = 2 := by obtain ⟨t, ht⟩ := heven; omega
    have hpower : n = 2 ^ n.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro r hr hrd
        have hupper := hmax r hr hrd
        have hlower := hr.two_le
        omega)
    have hk : 2 ≤ n.primeFactorsList.length := by
      by_contra h
      have hh : n.primeFactorsList.length = 0 ∨ n.primeFactorsList.length = 1 := by omega
      rcases hh with hh | hh <;> simp only [hh, pow_zero, pow_one] at hpower <;> omega
    have hfour : 4 ∣ n := by
      rw [hpower]
      refine ⟨2 ^ (n.primeFactorsList.length - 2), ?_⟩
      change 2 ^ n.primeFactorsList.length = 2 ^ 2 * 2 ^ (n.primeFactorsList.length - 2)
      rw [← pow_add]
      congr 1
      omega
    have heq : 4 = n := Even.eq_of_totient_eq_totient hfour (by decide)
      (by rw [hphi]; decide)
    omega
  · have hphi_lt : n.totient < 4 := by
      by_contra h
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ n.totient by omega)
      norm_num at hh
      omega
    have hphi : n.totient = 2 := by obtain ⟨t, ht⟩ := heven; omega
    have heq := Nat.eq_or_eq_of_totient_eq_totient hln (by rw [hphi]; decide)
    omega
  · have hphi_lt : n.totient < 5 := by
      by_contra h
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ n.totient by omega)
      norm_num at hh
      omega
    have hphi : n.totient = 4 := by omega
    have heq := Nat.eq_or_eq_of_totient_eq_totient hln (by rw [hphi]; decide)
    omega

end Atlas.OrderArithmetic

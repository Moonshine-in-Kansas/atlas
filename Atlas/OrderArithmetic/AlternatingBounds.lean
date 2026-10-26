import Atlas.OrderArithmetic.Orders
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Linarith

namespace Atlas.OrderArithmetic

/-- Exact division by two in the alternating formula. -/
theorem alternating_double {n : ℕ} (hn : 2 ≤ n) : 2 * (n.factorial / 2) = n.factorial :=
  Nat.mul_div_cancel' (Nat.dvd_factorial (by omega) hn)

/-- The elementary cutoff used in the alternating/Lie comparison. -/
theorem alternating_gt_eight_pow {n : ℕ} (hn : 20 ≤ n) : 8 ^ n < n.factorial / 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
    rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.dvd_factorial (by omega) (by omega))]
    rw [pow_succ]
    calc
      8 ^ n * 8 < (n.factorial / 2) * 8 := Nat.mul_lt_mul_of_pos_right ih (by omega)
      _ ≤ (n + 1) * (n.factorial / 2) := by
        rw [mul_comm (n + 1)]
        exact Nat.mul_le_mul_left _ (by omega)

/-- Once the Lie growth/valuation estimate gives this inequality, only degrees 5–19 remain. -/
theorem alternating_degree_lt_twenty {n : ℕ} (h : n.factorial / 2 < 8 ^ n) : n < 20 := by
  by_contra hn
  have := alternating_gt_eight_pow (by omega : 20 ≤ n)
  omega

/-- An absent odd prime bounds every potential alternating degree. -/
theorem alternating_degree_lt_missing_prime {n M p : ℕ} (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hM : ¬ p ∣ M) (h : n.factorial / 2 = M) : n < p := by
  by_contra hnp
  have hdiv : p ∣ n.factorial := Nat.dvd_factorial hp.pos (by omega)
  rw [← alternating_double hn, h] at hdiv
  rcases hp.dvd_mul.mp hdiv with htwo | hbad
  · have : p = 2 := ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp htwo).symm
    exact hp2 this
  · exact hM hbad

theorem alternating_order_injective {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n)
    (h : order (.alternating m) = order (.alternating n)) : m = n := by
  change m.factorial / 2 = n.factorial / 2 at h
  have hf : m.factorial = n.factorial := by
    rw [← alternating_double (by omega : 2 ≤ m), ← alternating_double (by omega : 2 ≤ n), h]
  rcases lt_trichotomy m n with hlt | heq | hgt
  · have := Nat.factorial_lt_of_lt (by omega : 0 < m) hlt
    omega
  · exact heq
  · have := Nat.factorial_lt_of_lt (by omega : 0 < n) hgt
    omega

end Atlas.OrderArithmetic

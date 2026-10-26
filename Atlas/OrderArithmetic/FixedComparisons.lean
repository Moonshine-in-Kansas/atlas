import Atlas.OrderArithmetic.AlternatingBounds
import Mathlib.Tactic.IntervalCases

namespace Atlas.OrderArithmetic

/-- An explicit odd prime absent from each fixed order. -/
def missingPrime : FixedLabel → ℕ
  | .M11 => 7
  | .M12 => 7
  | .M22 => 13
  | .M23 => 13
  | .M24 => 13
  | .J1 => 13
  | .J2 => 11
  | .J3 => 7
  | .J4 => 13
  | .HS => 13
  | .McL => 13
  | .He => 11
  | .Ru => 11
  | .Suz => 17
  | .ON => 13
  | .Co3 => 13
  | .Co2 => 13
  | .Fi22 => 17
  | .HN => 13
  | .Ly => 13
  | .Th => 11
  | .Fi23 => 19
  | .Co1 => 17
  | .Fi24prime => 19
  | .Baby => 29
  | .Monster => 37
  | .Tits => 7

theorem missingPrime_prime (s : FixedLabel) : (missingPrime s).Prime := by
  cases s <;> norm_num [missingPrime]

theorem missingPrime_ne_two (s : FixedLabel) : missingPrime s ≠ 2 := by
  cases s <;> norm_num [missingPrime]

theorem missingPrime_not_dvd (s : FixedLabel) : ¬ missingPrime s ∣ fixedOrder s := by
  cases s <;> norm_num [missingPrime, fixedOrder]

theorem alternating_ne_fixed {n : ℕ} (hn : 5 ≤ n) (s : FixedLabel) :
    order (.alternating n) ≠ order (.fixed s) := by
  intro h
  have hb := alternating_degree_lt_missing_prime (by omega : 2 ≤ n)
    (missingPrime_prime s) (missingPrime_ne_two s) (missingPrime_not_dvd s) h
  cases s <;> simp only [missingPrime] at hb
  all_goals interval_cases n <;> norm_num [order, fixedOrder, Nat.factorial] at h

theorem cyclic_ne_fixed {p : ℕ} (hp : p.Prime) (s : FixedLabel) :
    order (.cyclic p) ≠ order (.fixed s) := by
  intro h
  change p = fixedOrder s at h
  exact fixedOrder_not_prime s (h ▸ hp)

end Atlas.OrderArithmetic

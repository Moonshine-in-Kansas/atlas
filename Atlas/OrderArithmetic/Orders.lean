import Atlas.OrderArithmetic.FixedData
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic

namespace Atlas.OrderArithmetic
open scoped BigOperators

/-- Unitary signs are interpreted by parity, never by natural-number negation. -/
def unitaryFactor (q i : ℕ) : ℕ := if Even i then q ^ i - 1 else q ^ i + 1

def fieldSize : RawEntry → ℕ
  | .linear _ q | .unitary _ q | .B _ q | .C _ q | .Dplus _ q | .Dminus _ q
  | .G2 q | .F4 q | .E6 q | .E7 q | .E8 q | .twistedE6 q | .trialityD4 q
  | .suzuki q | .smallRee q | .largeRee q => q
  | _ => 1

def characteristicExponent : RawEntry → ℕ
  | .linear d _ | .unitary d _ => d * (d - 1) / 2
  | .B r _ | .C r _ => r ^ 2
  | .Dplus r _ | .Dminus r _ => r * (r - 1)
  | .G2 _ => 6
  | .F4 _ => 24
  | .E6 _ | .twistedE6 _ => 36
  | .E7 _ => 63
  | .E8 _ => 120
  | .trialityD4 _ | .largeRee _ => 12
  | .suzuki _ => 2
  | .smallRee _ => 3
  | _ => 0

def residual : RawEntry → ℕ
  | .linear d q => ∏ i ∈ Finset.Icc 2 d, (q ^ i - 1)
  | .unitary d q => ∏ i ∈ Finset.Icc 2 d, unitaryFactor q i
  | .B r q | .C r q => ∏ i ∈ Finset.Icc 1 r, (q ^ (2 * i) - 1)
  | .Dplus r q => (q ^ r - 1) * ∏ i ∈ Finset.Icc 1 (r - 1), (q ^ (2 * i) - 1)
  | .Dminus r q => (q ^ r + 1) * ∏ i ∈ Finset.Icc 1 (r - 1), (q ^ (2 * i) - 1)
  | .G2 q => (q ^ 6 - 1) * (q ^ 2 - 1)
  | .F4 q => ∏ i ∈ ({2, 6, 8, 12} : Finset ℕ), (q ^ i - 1)
  | .E6 q => ∏ i ∈ ({2, 5, 6, 8, 9, 12} : Finset ℕ), (q ^ i - 1)
  | .E7 q => ∏ i ∈ ({2, 6, 8, 10, 12, 14, 18} : Finset ℕ), (q ^ i - 1)
  | .E8 q => ∏ i ∈ ({2, 8, 12, 14, 18, 20, 24, 30} : Finset ℕ), (q ^ i - 1)
  | .twistedE6 q => (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
  | .trialityD4 q => (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .suzuki q => (q ^ 2 + 1) * (q - 1)
  | .smallRee q => (q ^ 3 + 1) * (q - 1)
  | .largeRee q => (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
  | _ => 1

def denominator : RawEntry → ℕ
  | .linear d q => Nat.gcd d (q - 1)
  | .unitary d q => Nat.gcd d (q + 1)
  | .B _ q | .C _ q | .E7 q => Nat.gcd 2 (q - 1)
  | .Dplus r q => Nat.gcd 4 (q ^ r - 1)
  | .Dminus r q => Nat.gcd 4 (q ^ r + 1)
  | .E6 q => Nat.gcd 3 (q - 1)
  | .twistedE6 q => Nat.gcd 3 (q + 1)
  | _ => 1

def numerator (x : RawEntry) : ℕ := fieldSize x ^ characteristicExponent x * residual x

/-- Integer formulas; no assertion that a group has this cardinality is used. -/
def order : RawEntry → ℕ
  | .cyclic p => p
  | .alternating n => n.factorial / 2
  | .fixed s => fixedOrder s
  | x => numerator x / denominator x

@[simp] theorem order_B_eq_C (r q : ℕ) : order (.B r q) = order (.C r q) := rfl

end Atlas.OrderArithmetic

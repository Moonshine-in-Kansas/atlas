import Atlas.OrderArithmetic.Orders
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Atlas.OrderArithmetic

/-- Among triangular characteristic exponents of positive-rank linear and
unitary labels, the only prime value occurs in dimension three. -/
theorem triangular_exponent_prime_dimension {d : ℕ} (hd : 2 ≤ d)
    (hp : (d * (d - 1) / 2).Prime) : d = 3 := by
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨t, ht⟩ := he
    have heq : d * (d - 1) / 2 = t * (d - 1) := by
      have hm : d * (d - 1) = (t * (d - 1)) * 2 := by rw [ht]; ring
      rw [hm, Nat.mul_div_cancel _ (by decide : 0 < 2)]
    rw [heq] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨_, h⟩ | ⟨_, h⟩
    · have htwo : d = 2 := by omega
      subst d
      have htone : t = 1 := by omega
      subst t
      norm_num at hp
    · have htwo : d = 2 := by omega
      subst d
      have htone : t = 1 := by omega
      subst t
      norm_num at hp
  · obtain ⟨t, ht⟩ := ho
    have hpred : d - 1 = 2 * t := by omega
    have heq : d * (d - 1) / 2 = d * t := by
      rw [hpred, show d * (2 * t) = (d * t) * 2 by ring,
        Nat.mul_div_cancel _ (by decide : 0 < 2)]
    rw [heq] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · omega

/-- The characteristic-two prime-exponent branch has exactly one admissible
label once exponents one and two have been removed. -/
theorem binary_prime_exponent_label {x : RawEntry} (hx : Admissible x)
    (hl : IsLie x) (hq : fieldSize x = 2)
    (hp : (characteristicExponent x).Prime) (ha : 3 ≤ characteristicExponent x) :
    x = .linear 3 2 := by
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear d q =>
    have hd : d = 3 := triangular_exponent_prime_dimension hx.1 hp
    have hq' : q = 2 := hq
    subst d
    subst q
    rfl
  | unitary d q =>
    have hd : d = 3 := triangular_exponent_prime_dimension (by have := hx.1; omega) hp
    have hq' : q = 2 := hq
    subst d
    subst q
    exact (hx.2.2 ⟨rfl, rfl⟩).elim
  | B r q | C r q =>
    have hr : r ≠ 1 := by have := hx.1; omega
    exact (Nat.not_prime_mul hr hr (by simpa only [characteristicExponent, pow_two] using hp)).elim
  | Dplus r q | Dminus r q =>
    have hr : r ≠ 1 := by have := hx.1; omega
    have hr' : r - 1 ≠ 1 := by have := hx.1; omega
    exact (Nat.not_prime_mul hr hr' hp).elim
  | smallRee q =>
    obtain ⟨m, hm, hqm⟩ := hx
    have hthree : 3 ≤ 3 ^ (2 * m + 1) := Nat.le_pow (by omega)
    change q = 2 at hq
    omega
  | suzuki q => norm_num [characteristicExponent] at ha
  | G2 _ | F4 _ | E6 _ | E7 _ | E8 _ | twistedE6 _ | trialityD4 _ | largeRee _ =>
    norm_num [characteristicExponent] at hp

end Atlas.OrderArithmetic

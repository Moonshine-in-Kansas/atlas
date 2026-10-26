import Mathlib.Data.Nat.Factorization.Basic
import Lean.Elab.Tactic.Omega

namespace Atlas.OrderArithmetic

/-- Exact removal of a central divisor, before any valuation calculation. -/
theorem quotient_factorization {q a R d : ℕ} (hd : d ∣ R) :
    (q ^ a * R) / d = q ^ a * (R / d) := Nat.mul_div_assoc _ hd

/-- The characteristic valuation calculation shared by every ordinary formula. -/
theorem characteristic_valuation {p f a R d : ℕ} (hp : p.Prime)
    (hd : d ∣ R) (hR : ¬ p ∣ R) :
    (((p ^ f) ^ a * R) / d).factorization p = f * a := by
  have hquot : ¬ p ∣ R / d := fun h => hR (h.trans (Nat.div_dvd_of_dvd hd))
  have hne : R / d ≠ 0 := by
    intro hz
    exact hquot (hz ▸ dvd_zero p)
  rw [quotient_factorization hd, ← pow_mul,
    Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hne]
  simp only [Finsupp.add_apply, Nat.factorization_pow_self hp,
    Nat.factorization_eq_zero_of_not_dvd hquot, add_zero]

/-- Characteristic primes cannot divide a minus factor. -/
theorem prime_not_dvd_pow_sub_one {p q j : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (hpq : p ∣ q) (hj : 1 ≤ j) : ¬ p ∣ q ^ j - 1 := by
  intro h
  have hpow : p ∣ q ^ j := hpq.trans (dvd_pow_self q (by omega))
  have hpos : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
  have hone : q ^ j - (q ^ j - 1) = 1 := by omega
  exact hp.not_dvd_one (hone ▸ Nat.dvd_sub hpow h)

/-- Characteristic primes cannot divide a plus factor. -/
theorem prime_not_dvd_pow_add_one {p q j : ℕ} (hp : p.Prime)
    (hpq : p ∣ q) (hj : 1 ≤ j) : ¬ p ∣ q ^ j + 1 := by
  intro h
  have hpow : p ∣ q ^ j := hpq.trans (dvd_pow_self q (by omega))
  have hsub := Nat.dvd_sub h hpow
  simpa using hp.not_dvd_one (by simpa using hsub)

end Atlas.OrderArithmetic

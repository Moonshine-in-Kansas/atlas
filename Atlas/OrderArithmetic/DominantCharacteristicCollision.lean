import Atlas.OrderArithmetic.SameCharacteristic

namespace Atlas.OrderArithmetic

/-- Strict dominance identifies the defining prime from the integer order.
The hypotheses are explicit so this reduction does not presume any unfinished
small-rank dominance theorem. -/
theorem defining_primes_eq_of_dominance {x y : RawEntry} {p r f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hr : r.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = r ^ g)
    (dx : ∀ l : ℕ, l.Prime → ¬ l ∣ fieldSize x →
      l ^ (order x).factorization l < fieldSize x ^ characteristicExponent x)
    (dy : ∀ l : ℕ, l.Prime → ¬ l ∣ fieldSize y →
      l ^ (order y).factorization l < fieldSize y ^ characteristicExponent y)
    (he : order x = order y) : p = r := by
  by_contra hpr
  have hrx : ¬ r ∣ fieldSize x := by
    rw [hqx]
    exact fun hd => hpr (Nat.prime_eq_prime_of_dvd_pow hr hp hd).symm
  have hpy : ¬ p ∣ fieldSize y := by
    rw [hqy]
    exact fun hd => hpr (Nat.prime_eq_prime_of_dvd_pow hp hr hd)
  have hdx := dx r hr hrx
  have hdy := dy p hp hpy
  rw [he, order_characteristic_valuation hy hly hr hg hqy, hqx, ← pow_mul] at hdx
  rw [← he, order_characteristic_valuation hx hlx hp hf hqx, hqy, ← pow_mul] at hdy
  exact (not_lt_of_ge (le_of_lt hdx)) hdy

/-- Equal orders with strict characteristic dominance reduce to the already
verified unbounded same-characteristic collision theorem. -/
theorem collision_of_dominant_characteristics {x y : RawEntry} {p r f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hr : r.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = r ^ g)
    (dx : ∀ l : ℕ, l.Prime → ¬ l ∣ fieldSize x →
      l ^ (order x).factorization l < fieldSize x ^ characteristicExponent x)
    (dy : ∀ l : ℕ, l.Prime → ¬ l ∣ fieldSize y →
      l ^ (order y).factorization l < fieldSize y ^ characteristicExponent y)
    (he : order x = order y) : Collision x y := by
  have hpr := defining_primes_eq_of_dominance hx hy hlx hly hp hr hf hg hqx hqy dx dy he
  subst r
  exact same_characteristic_collision hx hy hlx hly hp hf hg hqx hqy he

end Atlas.OrderArithmetic

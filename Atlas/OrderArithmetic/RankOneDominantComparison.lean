import Atlas.OrderArithmetic.RankOneCharacteristic
import Atlas.OrderArithmetic.MersenneComparison
import Atlas.OrderArithmetic.SameCharacteristic
import Atlas.OrderArithmetic.FiniteTables
import Atlas.OrderArithmetic.ElementaryClassification

namespace Atlas.OrderArithmetic

/-- A competing defining-prime contribution at least q suffices to classify
an equal order with L2(q). No dominance theorem is assumed for the competitor. -/
theorem linear_two_collision_of_competing_contribution {q p r f g : ℕ} {y : RawEntry}
    (hx : Admissible (.linear 2 q)) (hy : Admissible y) (hly : IsLie y)
    (hp : p.Prime) (hr : r.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : q = p ^ f) (hqy : fieldSize y = r ^ g)
    (he : order (.linear 2 q) = order y)
    (hlarge : q ≤ r ^ (order (.linear 2 q)).factorization r) :
    Collision (.linear 2 q) y := by
  by_cases hpr : p = r
  · subst r
    exact same_characteristic_collision hx hy (by trivial) hly hp hf hg hqx hqy he
  have hrq : ¬ r ∣ q := by
    rw [hqx]
    exact fun hd => hpr (Nat.prime_eq_prime_of_dvd_pow hr hp hd).symm
  have hq2 : 2 ≤ q := primePower_two_le hx.2.1
  by_cases hp2 : p = 2
  · subst p
    have hr2 : r ≠ 2 := Ne.symm hpr
    have hoq : Even q := by
      rw [hqx]
      exact (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
    rcases linear_two_even_cross_large_forces_fermat_or_eight hx hf hqx hr hrq hlarge with hprime | h8
    · have hle := linear_two_odd_cross_contribution_le hx hr hr2 hrq
      have hodd := Nat.odd_iff.mp ((hr.odd_of_ne_two hr2).pow
        (n := (order (.linear 2 q)).factorization r))
      have heven := Nat.even_iff.mp hoq
      have hcon : r ^ (order (.linear 2 q)).factorization r = q + 1 := by omega
      have hvpos : (order (.linear 2 q)).factorization r ≠ 0 := by
        intro hh
        rw [hh, pow_zero] at hcon
        omega
      have hrdvd : r ∣ q + 1 := hcon ▸ dvd_pow_self r hvpos
      have hrfield : r = q + 1 := (Nat.prime_dvd_prime_iff_eq hr hprime).mp hrdvd
      have hq4 : 4 ≤ q := by
        have hnot := hx.2.2
        omega
      obtain ⟨hqeq, hyeq⟩ := fermat_adjacent_characteristic_match hy hly hq4 hoq hprime hg
        (by simpa [hrfield] using hqy) he
      left
      rw [hqeq, hyeq]
      norm_num [normalize]
    · have hy8 : y = .linear 2 8 := (order_eq_504_iff hy hly).mp (by
        rw [← he, h8]
        exact regression_504)
      left
      rw [h8, hy8]
  · have hoq : Odd q := by rw [hqx]; exact (hp.odd_of_ne_two hp2).pow
    obtain ⟨hr2, hqprime, k, hk, hkq⟩ :=
      linear_two_odd_cross_large_forces_mersenne_prime hx hoq hr hrq hlarge
    have hqm : q = 2 ^ k - 1 := by omega
    have hprime : (2 ^ k - 1).Prime := by simpa [← hqm] using hqprime
    have hxm : Admissible (.linear 2 (2 ^ k - 1)) := by simpa [← hqm] using hx
    obtain ⟨hk3, hy3⟩ := mersenne_binary_characteristic_match hprime hxm hy hly hg
      (by simpa [hr2] using hqy) (by simpa [← hqm] using he)
    have hq7 : q = 7 := by rw [hk3] at hkq; norm_num at hkq; omega
    left
    rw [hq7, hy3]
    norm_num [normalize]

/-- Strict dominance of just the competing group supplies the comparison
hypothesis needed for the rank-one exception analysis. -/
theorem linear_two_collision_of_dominant_competitor {q p r f g : ℕ} {y : RawEntry}
    (hx : Admissible (.linear 2 q)) (hy : Admissible y) (hly : IsLie y)
    (hp : p.Prime) (hr : r.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : q = p ^ f) (hqy : fieldSize y = r ^ g)
    (dy : ∀ l : ℕ, l.Prime → ¬ l ∣ fieldSize y →
      l ^ (order y).factorization l < fieldSize y ^ characteristicExponent y)
    (he : order (.linear 2 q) = order y) : Collision (.linear 2 q) y := by
  by_cases hpr : p = r
  · subst r
    exact same_characteristic_collision hx hy (by trivial) hly hp hf hg hqx hqy he
  have hpy : ¬ p ∣ fieldSize y := by
    rw [hqy]
    exact fun hd => hpr (Nat.prime_eq_prime_of_dvd_pow hp hr hd)
  have hxp : p ^ (order (.linear 2 q)).factorization p = q := by
    rw [order_characteristic_valuation hx (by trivial) hp hf hqx]
    simp [characteristicExponent, hqx]
  have hyr : r ^ (order y).factorization r = fieldSize y ^ characteristicExponent y := by
    rw [order_characteristic_valuation hy hly hr hg hqy, hqy, pow_mul]
  have hh := dy p hp hpy
  rw [← he, hxp] at hh
  have hlarge : q ≤ r ^ (order (.linear 2 q)).factorization r := by
    rw [he, hyr]
    exact hh.le
  exact linear_two_collision_of_competing_contribution hx hy hly hp hr hf hg hqx hqy he hlarge

/-- The two rank-one sides need no dominance hypothesis: compare their field
sizes and use the larger field as the competing characteristic contribution. -/
theorem linear_two_equal_order_collision {q s p r f g : ℕ}
    (hx : Admissible (.linear 2 q)) (hy : Admissible (.linear 2 s))
    (hp : p.Prime) (hr : r.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : q = p ^ f) (hqy : s = r ^ g)
    (he : order (.linear 2 q) = order (.linear 2 s)) :
    Collision (.linear 2 q) (.linear 2 s) := by
  have hxp : p ^ (order (.linear 2 q)).factorization p = q := by
    rw [order_characteristic_valuation hx (by trivial) hp hf hqx]
    simp [characteristicExponent, hqx]
  have hyr : r ^ (order (.linear 2 s)).factorization r = s := by
    rw [order_characteristic_valuation hy (by trivial) hr hg hqy]
    simp [characteristicExponent, hqy]
  rcases le_total q s with hqs | hsq
  · exact linear_two_collision_of_competing_contribution hx hy (by trivial) hp hr hf hg hqx hqy he
      (by rw [he, hyr]; exact hqs)
  · exact collision_symm (linear_two_collision_of_competing_contribution hy hx (by trivial)
      hr hp hg hf hqy hqx he.symm (by rw [← he, hxp]; exact hsq))

end Atlas.OrderArithmetic

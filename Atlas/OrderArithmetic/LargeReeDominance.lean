import Atlas.OrderArithmetic.TwistedE6Dominance

namespace Atlas.OrderArithmetic

private theorem odd_prime_plus_not_minus {l n : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hn : 1 ≤ n) (hp : l ∣ n + 1) :
    ¬ l ∣ n - 1 := by
  intro hm
  have hh := Nat.dvd_sub hp hm
  have he : n + 1 - (n - 1) = 2 := by omega
  rw [he] at hh
  exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hh)

/-- The two large Ree residual branches are separated by the sixth plus factor.
A prime in that factor cannot also occur in the cubic plus or linear minus
factor, so its entire power lies in a product of at most two factors. -/
theorem largeRee_odd_prime_power_residual {q l e : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hl2 : l ≠ 2)
    (hd : l ^ e ∣ (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)) :
    l ^ e ∣ (q ^ 6 + 1) * (q ^ 4 - 1) ∨
      l ^ e ∣ (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) := by
  by_cases hA : l ∣ q ^ 6 + 1
  · have hn := odd_prime_plus_not_minus hl hl2
      (Nat.one_le_pow _ _ (by omega : 1 ≤ q)) hA
    have hC : ¬ l ∣ q ^ 3 + 1 := by
      intro hh
      exact hn (hh.trans (plus_factor_dvd_even_minus (by omega : 1 ≤ q) 3))
    have hD : ¬ l ∣ q - 1 := by
      intro hh
      exact hn (hh.trans (Nat.sub_one_dvd_pow_sub_one q 6))
    have hdABC := hl.prime.pow_dvd_of_dvd_mul_right e hD hd
    exact Or.inl (hl.prime.pow_dvd_of_dvd_mul_right e hC hdABC)
  · apply Or.inr
    have he : (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) =
        (q ^ 6 + 1) * ((q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)) := by ring
    rw [he] at hd
    exact hl.prime.pow_dvd_of_dvd_mul_left e hA hd

/-- Every cross-characteristic prime contribution to a large Ree order is
strictly smaller than its characteristic contribution q¹². -/
theorem largeRee_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.largeRee q)) (hl : l.Prime) (hl2 : l ≠ 2) :
    l ^ (order (.largeRee q)).factorization l < q ^ 12 := by
  obtain ⟨m, hm, hqfield⟩ := hx
  have hq : 2 ≤ q := by
    have hb : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hqfield]
    omega
  have hlq : ¬ l ∣ q := by
    intro hh
    rw [hqfield] at hh
    exact hl2 (Nat.prime_eq_prime_of_dvd_pow hl Nat.prime_two hh)
  have hdiv := cross_prime_order_contribution_dvd_residual
    (show Admissible (.largeRee q) from ⟨m, hm, hqfield⟩) (by trivial) hl hlq
  have hplus_bound : ∀ k : ℕ, q ^ k + 1 ≤ q ^ (k + 1) := by
    intro k
    have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
    have hm := Nat.mul_le_mul_left (q ^ k) hq
    rw [pow_succ]
    nlinarith
  have hBpos : 0 < q ^ 4 - 1 := by
    have hb : q ≤ q ^ 4 := by simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 1 ≤ 4)
    omega
  rcases largeRee_odd_prime_power_residual hq hl hl2 hdiv with hAB | hBCD
  · have hb := Nat.le_of_dvd (Nat.mul_pos (by omega : 0 < q ^ 6 + 1) hBpos) hAB
    have hbound : (q ^ 6 + 1) * (q ^ 4 - 1) ≤ q ^ 11 := by
      calc
        _ ≤ q ^ 7 * q ^ 4 := Nat.mul_le_mul (hplus_bound 6) (Nat.sub_le _ _)
        _ = q ^ 11 := by rw [← pow_add]
    exact (hb.trans hbound).trans_lt
      ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide : 11 < 12))
  · have hb := Nat.le_of_dvd
      (Nat.mul_pos (Nat.mul_pos hBpos (by omega : 0 < q ^ 3 + 1))
        (by omega : 0 < q - 1)) hBCD
    have hbound : (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 9 := by
      calc
        _ ≤ q ^ 4 * q ^ 4 * q :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le _ _) (hplus_bound 3)) (Nat.sub_le _ _)
        _ = q ^ 9 := by ring
    exact (hb.trans hbound).trans_lt
      ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide : 9 < 12))

end Atlas.OrderArithmetic

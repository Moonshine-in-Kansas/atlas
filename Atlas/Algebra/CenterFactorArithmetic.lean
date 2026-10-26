import Atlas.Algebra.FiniteFieldSignSquares

/-! Pure integer identities relating the two parity descriptions of the
split type-D center factor. No group or root-system theorem is used. -/
namespace Atlas

private theorem gcd_four_pow_sub_one_of_even_base
    (q r : ℕ) (hq : 1 ≤ q) (hr : 0 < r) (he : q % 2 = 0) :
    Nat.gcd 4 (q ^ r - 1) = 1 := by
  have hp : 1 ≤ q ^ r := one_le_pow₀ hq
  have hp2 : q ^ r % 2 = 0 := by
    simp only [Nat.pow_mod, he, zero_pow (Nat.ne_of_gt hr), Nat.zero_mod]
  have ho : Odd (q ^ r - 1) := Nat.odd_iff.mpr (by omega)
  have hc : Nat.Coprime 4 (q ^ r - 1) := by
    simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using ho.coprime_two_left.pow_left 2
  exact hc

/-- For positive bases and odd exponents, the fourth-root factor is unchanged. -/
theorem gcd_four_pow_sub_one_of_odd
    (q r : ℕ) (hq : 1 ≤ q) (hr : Odd r) :
    Nat.gcd 4 (q ^ r - 1) = Nat.gcd 4 (q - 1) := by
  have hpos : 0 < r := hr.pos
  rcases Nat.mod_two_eq_zero_or_one q with he | ho
  · rw [gcd_four_pow_sub_one_of_even_base q r hq hpos he]
    have hodd : Odd (q - 1) := Nat.odd_iff.mpr (by omega)
    have hc : Nat.Coprime 4 (q - 1) := by
      simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using hodd.coprime_two_left.pow_left 2
    exact (show Nat.gcd 4 (q - 1) = 1 from hc).symm
  · have hp : 1 ≤ q ^ r := one_le_pow₀ hq
    have hm : q ^ r % 4 = q % 4 := by
      rw [odd_power_mod_four q r ho, if_neg (Nat.not_even_iff_odd.mpr hr)]
    have hs : (q ^ r - 1) % 4 = (q - 1) % 4 := by omega
    rw [Nat.gcd_rec 4 (q ^ r - 1), Nat.gcd_rec 4 (q - 1), hs]

/-- For positive even exponents, the type-D fourth-root factor is the square
of the two-root factor, uniformly for even and odd bases. -/
theorem gcd_four_pow_sub_one_of_even
    (q r : ℕ) (hq : 1 ≤ q) (hr : 0 < r) (heven : Even r) :
    Nat.gcd 4 (q ^ r - 1) = Nat.gcd 2 (q - 1) ^ 2 := by
  rcases Nat.mod_two_eq_zero_or_one q with he | ho
  · rw [gcd_four_pow_sub_one_of_even_base q r hq hr he]
    have hodd : Odd (q - 1) := Nat.odd_iff.mpr (by omega)
    have hc : Nat.gcd 2 (q - 1) = 1 := hodd.coprime_two_left
    rw [hc]
    norm_num
  · have hp : 1 ≤ q ^ r := one_le_pow₀ hq
    have hm : q ^ r % 4 = 1 := by
      rw [odd_power_mod_four q r ho, if_pos heven]
    have hs : (q ^ r - 1) % 4 = 0 := by omega
    have hq2 : (q - 1) % 2 = 0 := by omega
    rw [Nat.gcd_rec 4 (q ^ r - 1), hs, Nat.gcd_rec 2 (q - 1), hq2]
    norm_num

end Atlas

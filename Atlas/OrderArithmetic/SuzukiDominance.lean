import Atlas.OrderArithmetic.RankOneDominance

namespace Atlas.OrderArithmetic

/-- The Tits-square relation gives the exact two-factor splitting of q²+1.
The smaller factor uses natural subtraction only under t≤q. -/
theorem suzuki_quadratic_factor {q t : ℕ} (htq : t ≤ q) (ht : t ^ 2 = 2 * q) :
    q ^ 2 + 1 = (q + t + 1) * (q - t + 1) := by
  have hs := Nat.sub_add_cancel htq
  have hm := congrArg (fun u : ℕ => u * (q + t + 1)) hs
  nlinarith

/-- For an odd prime not dividing the Tits square root, the entire prime power
in a Suzuki residual lies in one of its three pairwise prime-separated factors. -/
theorem suzuki_odd_prime_power_residual {q t l e : ℕ}
    (hq : 2 ≤ q) (htq : t ≤ q) (ht : t ^ 2 = 2 * q)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlt : ¬ l ∣ t)
    (hd : l ^ e ∣ (q ^ 2 + 1) * (q - 1)) :
    l ^ e ∣ q - 1 ∨ l ^ e ∣ q + t + 1 ∨ l ^ e ∣ q - t + 1 := by
  have hA : l ∣ q - 1 → ¬ l ∣ q ^ 2 + 1 := by
    intro hm hp
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have hs2 := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega))
    have he : q ^ 2 - 1 = (q - 1) * (q + 1) := by nlinarith
    have hminus : l ∣ q ^ 2 - 1 := by
      rw [he]
      exact dvd_mul_of_dvd_left hm _
    have htwo := Nat.dvd_sub hp hminus
    have hdiff : q ^ 2 + 1 - (q ^ 2 - 1) = 2 := by omega
    rw [hdiff] at htwo
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl (by decide)).mp htwo)
  have hBC : l ∣ q + t + 1 → ¬ l ∣ q - t + 1 := by
    intro hB hC
    have hh := Nat.dvd_sub hB hC
    have he : q + t + 1 - (q - t + 1) = 2 * t := by omega
    rw [he] at hh
    rcases hl.dvd_mul.mp hh with htwo | htdiv
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl (by decide)).mp htwo)
    · exact hlt htdiv
  by_cases ha : l ∣ q - 1
  · exact Or.inl (hl.prime.pow_dvd_of_dvd_mul_left e (hA ha) hd)
  · have hquad := hl.prime.pow_dvd_of_dvd_mul_right e ha hd
    rw [suzuki_quadratic_factor htq ht] at hquad
    by_cases hb : l ∣ q + t + 1
    · exact Or.inr (Or.inl (hl.prime.pow_dvd_of_dvd_mul_right e (hBC hb) hquad))
    · exact Or.inr (Or.inr (hl.prime.pow_dvd_of_dvd_mul_left e hb hquad))

/-- The explicit Tits square root at an admissible Suzuki field size. -/
theorem suzuki_tits_square (m : ℕ) :
    (2 ^ (m + 1)) ^ 2 = 2 * (2 ^ (2 * m + 1)) := by
  rw [← pow_mul, show (m + 1) * 2 = (2 * m + 1) + 1 by omega, pow_succ]
  omega

/-- Every cross-characteristic prime contribution is strictly smaller than
q² in an admissible Suzuki order. This uses the exact Tits-square factorization,
not a generic estimate or a separate five-adic lifting argument. -/
theorem suzuki_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.suzuki q)) (hl : l.Prime) (hl2 : l ≠ 2) :
    l ^ (order (.suzuki q)).factorization l < q ^ 2 := by
  obtain ⟨m, hm, hqfield⟩ := hx
  let t := 2 ^ (m + 1)
  have hq8 : 8 ≤ q := by
    have hb : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hqfield]
    exact hb
  have htq : t ≤ q := by
    rw [hqfield]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have ht : t ^ 2 = 2 * q := by
    rw [hqfield]
    exact suzuki_tits_square m
  have hlq : ¬ l ∣ q := by
    intro hh
    rw [hqfield] at hh
    exact hl2 (Nat.prime_eq_prime_of_dvd_pow hl Nat.prime_two hh)
  have hlt : ¬ l ∣ t := by
    intro hh
    exact hl2 (Nat.prime_eq_prime_of_dvd_pow hl Nat.prime_two hh)
  have hlq2 : ¬ l ∣ q ^ 2 := fun hd => hlq (hl.dvd_of_dvd_pow hd)
  have hpos : 0 < order (.suzuki q) :=
    lie_order_pos ⟨m, hm, hqfield⟩ (by trivial)
  have hd : l ^ (order (.suzuki q)).factorization l ∣ order (.suzuki q) :=
    (hl.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  have hdfact : l ^ (order (.suzuki q)).factorization l ∣
      q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := by
    convert hd using 1 <;> simp only [order, numerator, fieldSize,
      characteristicExponent, residual, denominator, Nat.div_one]
  have hres := hl.prime.pow_dvd_of_dvd_mul_left _ hlq2 hdfact
  have hsq : 8 * q ≤ q ^ 2 := by
    simpa [pow_two, mul_comm] using Nat.mul_le_mul_left q hq8
  have hBlt : q + t + 1 < q ^ 2 := by nlinarith
  have hClt : q - t + 1 < q ^ 2 := by
    have hb := Nat.sub_le q t
    nlinarith
  rcases suzuki_odd_prime_power_residual (by omega : 2 ≤ q) htq ht hl hl2 hlt hres with
    hA | hB | hC
  · have hb := Nat.le_of_dvd (by omega : 0 < q - 1) hA
    omega
  · exact (Nat.le_of_dvd (Nat.succ_pos (q + t)) hB).trans_lt hBlt
  · exact (Nat.le_of_dvd (Nat.succ_pos (q - t)) hC).trans_lt hClt

end Atlas.OrderArithmetic

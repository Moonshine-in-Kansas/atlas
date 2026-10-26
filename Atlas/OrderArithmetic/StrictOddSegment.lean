import Atlas.OrderArithmetic.ValuationSupport

namespace Atlas.OrderArithmetic

theorem odd_prime_minus_block_contribution_lt_field_power {l q e t : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (he : 1 ≤ e)
    (hdiv : l ∣ q ^ e - 1) (ht : 1 ≤ t) :
    l ^ (∏ j ∈ Finset.range t, (q ^ (e * (j + 1)) - 1)).factorization l <
      q ^ ((e + 1) * t) := by
  have hqe : 0 < q ^ e := pow_pos (by omega) _
  have hs : q ^ e - 1 < q ^ e := by omega
  have hp : (q ^ e - 1) ^ t < (q ^ e) ^ t :=
    Nat.pow_lt_pow_left hs (by omega)
  calc
    _ ≤ (q ^ e - 1) ^ t * 2 ^ t :=
      odd_prime_minus_block_contribution_le hl hl2 hq he hdiv t
    _ < (q ^ e) ^ t * 2 ^ t := Nat.mul_lt_mul_of_pos_right hp (by positivity)
    _ ≤ (q ^ e) ^ t * q ^ t := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq t)
    _ = q ^ ((e + 1) * t) := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- The odd-prime segment bound is strict for every nonempty segment,
including the case where the prime divides none of its factors. -/
theorem odd_cross_prime_minus_segment_contribution_lt {l q d : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (hlq : ¬ l ∣ q) (hd : 1 ≤ d) :
    l ^ (∏ i ∈ Finset.Icc 1 d, (q ^ i - 1)).factorization l < q ^ (2 * d) := by
  letI : Fact l.Prime := ⟨hl⟩
  let e := orderOf (q : ZMod l)
  have hn : (q : ZMod l) ≠ 0 := fun hh => hlq ((ZMod.natCast_eq_zero_iff q l).mp hh)
  have hediv : e ∣ l - 1 := ZMod.orderOf_dvd_card_sub_one hn
  have he : 1 ≤ e := Nat.pos_of_dvd_of_pos hediv (by have := hl.two_le; omega)
  have hs : ∀ i : ℕ, 1 ≤ i → (l ∣ q ^ i - 1 ↔ e ∣ i) := by
    intro i hi
    change l ∣ q ^ i - 1 ↔ orderOf (q : ZMod l) ∣ i
    rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff (q ^ i - 1) l,
      Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 1 ≤ q)),
      Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  have hdiv : l ∣ q ^ e - 1 := (hs e he).mpr (dvd_refl e)
  by_cases ht : d / e = 0
  · rw [odd_prime_minus_segment_valuation hl hl2 hq he hs, ht]
    simp only [zero_mul, Nat.factorial_zero, Nat.factorization_one, Finsupp.zero_apply,
      zero_add, pow_zero]
    have hp : q ≤ q ^ (2 * d) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 1 ≤ 2 * d)
    omega
  · rw [odd_prime_minus_segment_valuation hl hl2 hq he hs,
      ← odd_prime_minus_block_valuation hl hl2 hq he hdiv]
    have hh := odd_prime_minus_block_contribution_lt_field_power hl hl2 hq he hdiv
      (Nat.one_le_iff_ne_zero.mpr ht)
    have het : e * (d / e) ≤ d := by
      have := Nat.div_mul_le_self d e
      nlinarith
    have ht' : d / e ≤ d := Nat.div_le_self d e
    exact hh.trans_le (Nat.pow_le_pow_right (by omega : 0 < q) (by nlinarith))

end Atlas.OrderArithmetic

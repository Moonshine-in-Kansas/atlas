import Atlas.OrderArithmetic.UnitaryOddValuation
import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal

namespace Atlas.OrderArithmetic

theorem unitary_factor_double_lt_square_power {q e : ℕ} (hp : 3 ≤ q ^ e) :
    2 * unitaryFactor q e < q ^ (2 * e) := by
  have hb : unitaryFactor q e ≤ q ^ e + 1 := by
    unfold unitaryFactor
    split <;> omega
  have he : q ^ (2 * e) = (q ^ e) ^ 2 := by rw [← pow_mul]; congr 1; omega
  rw [he]
  nlinarith

theorem unitary_odd_prime_block_contribution_lt {l q e t : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (hlq : ¬ l ∣ q)
    (he : 1 ≤ e) (hdiv : l ∣ unitaryFactor q e) (ht : 1 ≤ t) (hpow : 3 ≤ q ^ e) :
    l ^ (∏ j ∈ Finset.range t, unitaryFactor q (e * (j + 1))).factorization l <
      q ^ (2 * e * t) := by
  have hb := unitary_odd_prime_block_contribution_le hl hl2 hq hlq he hdiv t
  have hp := Nat.pow_lt_pow_left (unitary_factor_double_lt_square_power hpow) (by omega : t ≠ 0)
  have hleft : (2 * unitaryFactor q e) ^ t = (unitaryFactor q e) ^ t * 2 ^ t := by
    rw [mul_pow, mul_comm]
  have hright : (q ^ (2 * e)) ^ t = q ^ (2 * e * t) := by rw [← pow_mul]
  rw [hleft, hright] at hp
  exact hb.trans_lt hp

/-- Strict unitary segment control at any signed support index with q^e≥3. -/
theorem unitary_odd_prime_segment_contribution_lt {l q e d : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (hlq : ¬ l ∣ q)
    (he : 1 ≤ e) (hsupport : ∀ i : ℕ, l ∣ unitaryFactor q i ↔ e ∣ i)
    (hd : 1 ≤ d) (hpow : 3 ≤ q ^ e) :
    l ^ (∏ i ∈ Finset.Icc 1 d, unitaryFactor q i).factorization l < q ^ (2 * d) := by
  have hdiv := (hsupport e).mpr (dvd_refl e)
  by_cases ht : d / e = 0
  · rw [unitary_odd_prime_segment_valuation hl hl2 hq hlq he hsupport, ht]
    simp only [zero_mul, Nat.factorial_zero, Nat.factorization_one, Finsupp.zero_apply,
      zero_add, pow_zero]
    have hp : q ≤ q ^ (2 * d) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 1 ≤ 2 * d)
    omega
  · rw [unitary_odd_prime_segment_valuation hl hl2 hq hlq he hsupport,
      ← unitary_odd_prime_block_valuation hl hl2 hq hlq he hdiv]
    have hb := unitary_odd_prime_block_contribution_lt hl hl2 hq hlq he hdiv
      (Nat.one_le_iff_ne_zero.mpr ht) hpow
    have hmul : e * (d / e) ≤ d := by
      have := Nat.div_mul_le_self d e
      nlinarith
    exact hb.trans_le (Nat.pow_le_pow_right (by omega : 0 < q) (by nlinarith))

theorem unitary_odd_cross_segment_contribution_lt {l q d : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 3 ≤ q) (hlq : ¬ l ∣ q) (hd : 1 ≤ d) :
    l ^ (∏ i ∈ Finset.Icc 1 d, unitaryFactor q i).factorization l < q ^ (2 * d) := by
  letI : Fact l.Prime := ⟨hl⟩
  let e := orderOf (-(q : ZMod l))
  have hnq : (q : ZMod l) ≠ 0 := fun hh => hlq ((ZMod.natCast_eq_zero_iff q l).mp hh)
  have hn : -(q : ZMod l) ≠ 0 := neg_ne_zero.mpr hnq
  have hediv : e ∣ l - 1 := ZMod.orderOf_dvd_card_sub_one hn
  have he : 1 ≤ e := Nat.pos_of_dvd_of_pos hediv (by have := hl.two_le; omega)
  have hs : ∀ i : ℕ, l ∣ unitaryFactor q i ↔ e ∣ i := fun i =>
    unitaryFactor_dvd_iff_signed_order (by omega)
  have hp : q ≤ q ^ e := by simpa using Nat.pow_le_pow_right (by omega : 0 < q) he
  exact unitary_odd_prime_segment_contribution_lt hl hl2 (by omega) hlq he hs hd (by omega)

/-- Odd cross-primes are strictly dominated in all unitary dimensions at
least five over fields of size at least three. -/
theorem unitary_odd_cross_contribution_lt_of_five_le {d q l : ℕ}
    (hx : Admissible (.unitary d q)) (hd : 5 ≤ d) (hq : 3 ≤ q)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q) :
    l ^ (order (.unitary d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  have hnonzero : (∏ i ∈ Finset.Icc 1 d, unitaryFactor q i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (unitaryFactor_pos_of_two_le (by omega) (Finset.mem_Icc.mp hi).1).ne'
  have hdiv : residual (.unitary d q) ∣ ∏ i ∈ Finset.Icc 1 d, unitaryFactor q i := by
    apply Finset.prod_dvd_prod_of_subset
    intro i hi
    have hh := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  have hb := (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hnonzero hdiv).trans_lt
    (unitary_odd_cross_segment_contribution_lt hl hl2 hq hlq (by omega : 1 ≤ d))
  have he : 2 * d ≤ d * (d - 1) / 2 := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hp : 4 * d ≤ d * (d - 1) := by nlinarith
    omega
  exact hb.trans_le (Nat.pow_le_pow_right (by omega : 0 < q) he)

end Atlas.OrderArithmetic

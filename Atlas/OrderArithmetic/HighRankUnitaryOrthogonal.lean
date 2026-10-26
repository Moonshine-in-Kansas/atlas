import Atlas.OrderArithmetic.HigherRankTwoDominance

namespace Atlas.OrderArithmetic

/-- Transfer a residual divisibility statement to an upper bound on a
cross-prime contribution, without assuming a central quotient is coprime. -/
theorem cross_prime_contribution_le_of_residual_dvd {x : RawEntry} {l M : ℕ}
    (hx : Admissible x) (hLie : IsLie x) (hl : l.Prime)
    (hlq : ¬ l ∣ fieldSize x) (hM : M ≠ 0) (hd : residual x ∣ M) :
    l ^ (order x).factorization l ≤ l ^ M.factorization l := by
  have hp := (cross_prime_order_contribution_dvd_residual hx hLie hl hlq).trans hd
  exact Nat.pow_le_pow_right hl.pos ((hl.pow_dvd_iff_le_factorization hM).mp hp)

/-- Both unitary signs divide the corresponding even minus factor. -/
theorem unitary_factor_dvd_even_factor {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    unitaryFactor q i ∣ q ^ (2 * i) - 1 := by
  unfold unitaryFactor
  split
  · exact Nat.pow_sub_one_dvd_pow_sub_one q (dvd_mul_left i 2)
  · have hbase : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
    have hfactor : q ^ (2 * i) - 1 = (q ^ i - 1) * (q ^ i + 1) := by
      have hp : q ^ (2 * i) = (q ^ i) ^ 2 := by rw [← pow_mul]; congr 1; omega
      rw [hp]
      have hs := Nat.sub_add_cancel hbase
      have hs2 := Nat.sub_add_cancel (by nlinarith : 1 ≤ (q ^ i) ^ 2)
      nlinarith
    rw [hfactor]
    exact dvd_mul_left _ _

theorem unitary_residual_dvd_even_segment {d q : ℕ} (hq : 2 ≤ q) :
    residual (.unitary d q) ∣ ∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1) := by
  change (∏ i ∈ Finset.Icc 2 d, unitaryFactor q i) ∣ _
  have hd : (∏ i ∈ Finset.Icc 2 d, unitaryFactor q i) ∣
      ∏ i ∈ Finset.Icc 2 d, (q ^ (2 * i) - 1) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    exact unitary_factor_dvd_even_factor hq i
  apply hd.trans
  apply Finset.prod_dvd_prod_of_subset
  intro i hi
  have hh := Finset.mem_Icc.mp hi
  exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩

/-- The signed unitary residual admits a uniform coarse odd-prime bound. -/
theorem unitary_odd_cross_contribution_le {d q l : ℕ}
    (hx : Admissible (.unitary d q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hlq : ¬ l ∣ q) :
    l ^ (order (.unitary d q)).factorization l ≤ q ^ (4 * d) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have hh := cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq
    (even_minus_segment_ne_zero hq d) (unitary_residual_dvd_even_segment hq)
  have hb := odd_cross_prime_minus_segment_contribution_le hl hl2 hq2
    (fun hd => hlq (hl.dvd_of_dvd_pow hd)) d
  have hb' : l ^ (∏ i ∈ Finset.Icc 1 d, (q ^ (2 * i) - 1)).factorization l ≤
      q ^ (4 * d) := by
    have hp : (q ^ 2) ^ (2 * d) = q ^ (4 * d) := by
      rw [← pow_mul]; congr 1; omega
    rw [hp] at hb
    simpa only [pow_mul] using hb
  exact hh.trans hb'

theorem unitary_two_contribution_le {d q : ℕ}
    (hx : Admissible (.unitary d q)) (ho : Odd q) :
    2 ^ (order (.unitary d q)).factorization 2 ≤ q ^ (3 * d) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hn : ¬ 2 ∣ q := by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    have := Nat.odd_iff.mp ho
    omega
  exact (cross_prime_contribution_le_of_residual_dvd hx (by trivial) Nat.prime_two hn
    (even_minus_segment_ne_zero hq d) (unitary_residual_dvd_even_segment hq)).trans
      (two_contribution_even_segment_le hq ho d)

/-- Every cross-prime is strictly dominated in unitary dimension at least ten. -/
theorem unitary_cross_contribution_lt_of_ten_le {d q l : ℕ}
    (hx : Admissible (.unitary d q)) (hd : 10 ≤ d)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.unitary d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hb : l ^ (order (.unitary d q)).factorization l ≤ q ^ (4 * d) := by
    by_cases hl2 : l = 2
    · subst l
      have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
      exact (unitary_two_contribution_le hx ho).trans
        (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 3 * d ≤ 4 * d))
    · exact unitary_odd_cross_contribution_le hx hl hl2 hlq
  have hexp : 4 * d < d * (d - 1) / 2 := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hpoly : 8 * d + 2 ≤ d * (d - 1) := by nlinarith
    omega
  exact hb.trans_lt ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr hexp)

end Atlas.OrderArithmetic

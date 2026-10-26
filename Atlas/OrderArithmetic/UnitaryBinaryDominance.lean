import Atlas.OrderArithmetic.UnitaryOddDominance

namespace Atlas.OrderArithmetic

theorem unitary_binary_three_segment_valuation (d : ℕ) :
    (∏ i ∈ Finset.Icc 1 d, unitaryFactor 2 i).factorization 3 =
      d + d.factorial.factorization 3 := by
  have hs : ∀ i : ℕ, 3 ∣ unitaryFactor 2 i ↔ 1 ∣ i := by
    intro i
    rw [unitaryFactor_dvd_iff_signed_order (by decide : 2 ≤ (2 : ℕ))]
    have he : -(2 : ZMod 3) = 1 := by decide
    simp [he]
  have hh := unitary_odd_prime_segment_valuation (q := 2) (l := 3) (e := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) hs d
  have hv : (unitaryFactor 2 1).factorization 3 = 1 := by
    change (3 : ℕ).factorization 3 = 1
    exact (by decide : Nat.Prime 3).factorization_self
  simpa only [Nat.div_one, hv, mul_one] using hh

private theorem binary_three_factorial_power_lt {d : ℕ} (hd : 5 ≤ d) :
    3 ^ (d + d.factorial.factorization 3) < 2 ^ (d * (d - 1) / 2) := by
  by_cases hd7 : 7 ≤ d
  · have hv := factorial_valuation_bound (by decide : Nat.Prime 3) d
    have hval : 2 * d.factorial.factorization 3 ≤ d := by simpa using hv
    have hpos : d + d.factorial.factorization 3 ≠ 0 := by omega
    have hp := Nat.pow_lt_pow_left (by decide : (3 : ℕ) < 4) hpos
    have hfour : 4 ^ (d + d.factorial.factorization 3) =
        2 ^ (2 * (d + d.factorial.factorization 3)) := by
      rw [pow_mul]
      rfl
    rw [hfour] at hp
    have htri : 3 * d ≤ d * (d - 1) / 2 := by
      have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
      have hprod : 6 * d ≤ d * (d - 1) := by nlinarith
      omega
    exact hp.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega))
  · have hc : d = 5 ∨ d = 6 := by omega
    rcases hc with rfl | rfl
    · have hv : (Nat.factorial 5).factorization 3 = 1 := by
        change (3 * 40).factorization 3 = 1
        rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
          (by decide : Nat.Prime 3).factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 40)]
      rw [hv]
      decide
    · have hv : (Nat.factorial 6).factorization 3 = 2 := by
        change (3 ^ 2 * 80).factorization 3 = 2
        rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
          Nat.factorization_pow_self (by decide : Nat.Prime 3),
          Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 80)]
      rw [hv]
      decide

/-- Binary unitary fields need only one exceptional support branch: the prime
three. Its factorial valuation is bounded separately, including dimensions5,6. -/
theorem unitary_binary_cross_contribution_lt_of_five_le {d l : ℕ}
    (hx : Admissible (.unitary d 2)) (hd : 5 ≤ d)
    (hl : l.Prime) (hlq : ¬ l ∣ 2) :
    l ^ (order (.unitary d 2)).factorization l < 2 ^ (d * (d - 1) / 2) := by
  have hl2 : l ≠ 2 := by
    intro hh
    subst l
    exact hlq (dvd_refl 2)
  have hnonzero : (∏ i ∈ Finset.Icc 1 d, unitaryFactor 2 i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (unitaryFactor_pos_of_two_le (by decide) (Finset.mem_Icc.mp hi).1).ne'
  have hdiv : residual (.unitary d 2) ∣ ∏ i ∈ Finset.Icc 1 d, unitaryFactor 2 i := by
    apply Finset.prod_dvd_prod_of_subset
    intro i hi
    have hh := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  have ht := cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hnonzero hdiv
  by_cases hl3 : l = 3
  · subst l
    rw [unitary_binary_three_segment_valuation] at ht
    exact ht.trans_lt (binary_three_factorial_power_lt hd)
  · letI : Fact l.Prime := ⟨hl⟩
    let e := orderOf (-(2 : ZMod l))
    have hn : -(2 : ZMod l) ≠ 0 := neg_ne_zero.mpr
      (fun hh => hlq ((ZMod.natCast_eq_zero_iff 2 l).mp hh))
    have hediv : e ∣ l - 1 := ZMod.orderOf_dvd_card_sub_one hn
    have he : 1 ≤ e := Nat.pos_of_dvd_of_pos hediv (by have := hl.two_le; omega)
    have hs : ∀ i : ℕ, l ∣ unitaryFactor 2 i ↔ e ∣ i := fun i =>
      unitaryFactor_dvd_iff_signed_order (by decide)
    have he1 : e ≠ 1 := by
      intro hh
      have hdiv3 := (hs 1).mpr (by rw [hh])
      change l ∣ 3 at hdiv3
      exact hl3 ((Nat.prime_dvd_prime_iff_eq hl (by decide : Nat.Prime 3)).mp hdiv3)
    have he2 : 2 ≤ e := by omega
    have hp : 3 ≤ 2 ^ e := by
      have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he2
      norm_num at hh
      omega
    have hb := unitary_odd_prime_segment_contribution_lt hl hl2 (by decide) hlq he hs
      (by omega : 1 ≤ d) hp
    have htri : 2 * d ≤ d * (d - 1) / 2 := by
      have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
      have hprod : 4 * d ≤ d * (d - 1) := by nlinarith
      omega
    exact (ht.trans_lt hb).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) htri)

end Atlas.OrderArithmetic

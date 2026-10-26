import Atlas.OrderArithmetic.E6Dominance
import Atlas.OrderArithmetic.F4Dominance
import Atlas.OrderArithmetic.HighRankCharacteristic

namespace Atlas.OrderArithmetic

/-- The strict segment estimate also settles the boundary dimension seven. -/
theorem linear_cross_contribution_lt_of_seven_le {d q l : ℕ}
    (hx : Admissible (.linear d q)) (hd : 7 ≤ d)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear d q)).factorization l < q ^ (d * (d - 1) / 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hdiv := cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq
  have hsegment : l ^ (order (.linear d q)).factorization l ∣
      ∏ i ∈ Finset.Icc 1 d, (q ^ i - 1) := by
    apply hdiv.trans
    change (∏ i ∈ Finset.Icc 2 d, (q ^ i - 1)) ∣ _
    apply Finset.prod_dvd_prod_of_subset
    intro i hi
    have hh := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  have hbound := prime_power_dvd_minus_segment_lt hq hl hlq (by omega) hsegment
  have hexp : 3 * d ≤ d * (d - 1) / 2 := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have : 6 * d ≤ d * (d - 1) := by nlinarith
    omega
  exact hbound.trans_le (Nat.pow_le_pow_right (by omega : 0 < q) hexp)

/-- The strict odd-prime estimate settles the boundary C-rank four as well. -/
theorem symplectic_cross_contribution_lt_of_four_le {r q l : ℕ}
    (hx : Admissible (.C r q)) (hr : 4 ≤ r)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.C r q)).factorization l < q ^ (r ^ 2) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  by_cases h2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun h => hlq (even_iff_two_dvd.mp h))
    exact symplectic_two_contribution_lt_of_four_le hx ho hr
  · have hdiv := cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq
    have hv := (hl.pow_dvd_iff_le_factorization (even_minus_segment_ne_zero hq r)).mp hdiv
    have hb := odd_cross_prime_minus_segment_contribution_lt (q := q ^ 2) (d := r)
      hl h2 (by nlinarith) (fun h => hlq (hl.dvd_of_dvd_pow h)) (by omega)
    have hb' : l ^ (∏ i ∈ Finset.Icc 1 r, (q ^ (2 * i) - 1)).factorization l <
        q ^ (4 * r) := by
      simpa only [← pow_mul, show 2 * (2 * r) = 4 * r by omega] using hb
    exact ((Nat.pow_le_pow_right hl.pos hv).trans_lt hb').trans_le
      (Nat.pow_le_pow_right (by omega : 0 < q) (by nlinarith : 4 * r ≤ r ^ 2))

theorem odd_orthogonal_cross_contribution_lt_of_four_le {r q l : ℕ}
    (hx : Admissible (.B r q)) (hr : 4 ≤ r)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.B r q)).factorization l < q ^ (r ^ 2) := by
  rw [order_B_eq_C]
  exact symplectic_cross_contribution_lt_of_four_le hx hr hl hlq

end Atlas.OrderArithmetic

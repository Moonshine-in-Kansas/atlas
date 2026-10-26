import Atlas.OrderArithmetic.LinearFourDominance

namespace Atlas.OrderArithmetic

/-- The literal rank-two symplectic residual. -/
theorem symplectic_rank_two_residual {q : ℕ} (hq : 2 ≤ q) :
    residual (.C 2 q) = (q ^ 2 - 1) ^ 2 * (q ^ 2 + 1) := by
  have hs := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega : 1 ≤ q))
  have hs4 := Nat.sub_add_cancel (Nat.one_le_pow 4 q (by omega : 1 ≤ q))
  have he : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by nlinarith
  norm_num [residual, Finset.prod_Icc_succ_top, he]
  ring

/-- The central factor two cancels the additional binary contribution at
rank two. This is an exact valuation of the quotient order, not its residual. -/
theorem symplectic_rank_two_two_valuation {q : ℕ}
    (hx : Admissible (.C 2 q)) (ho : Odd q) :
    (order (.C 2 q)).factorization 2 = 2 * (q ^ 2 - 1).factorization 2 := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hnq : ¬ 2 ∣ q := fun hd => (by
    have hh := Nat.mod_eq_zero_of_dvd hd
    have hm := Nat.odd_iff.mp ho
    omega)
  have hnq4 : ¬ 2 ∣ q ^ 4 := fun hd => hnq (Nat.prime_two.dvd_of_dvd_pow hd)
  have hR : residual (.C 2 q) ≠ 0 := even_minus_segment_ne_zero hq 2
  have hnum : (numerator (.C 2 q)).factorization 2 = (residual (.C 2 q)).factorization 2 := by
    change (q ^ 4 * residual (.C 2 q)).factorization 2 = _
    rw [Nat.factorization_mul (pow_ne_zero 4 (by omega : q ≠ 0)) hR]
    simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnq4, zero_add]
  have hden : denominator (.C 2 q) = 2 := by
    change Nat.gcd 2 (q - 1) = 2
    apply Nat.gcd_eq_left
    apply Nat.dvd_of_mod_eq_zero
    have hm := Nat.odd_iff.mp ho
    omega
  rw [lie_order_eq (by trivial : IsLie (.C 2 q)),
    Nat.factorization_div (denominator_dvd_numerator hx), Finsupp.tsub_apply,
    hnum, hden, Nat.prime_two.factorization_self]
  change (∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1)).factorization 2 - 1 = _
  rw [two_valuation_even_segment hq ho]
  norm_num

/-- All cross-characteristic contributions in rank two are strictly smaller
than q⁴, including the binary contribution after central cancellation. -/
theorem symplectic_rank_two_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.C 2 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.C 2 q)).factorization l < q ^ 4 := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hq2 : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hApos : 0 < q ^ 2 - 1 := by omega
  have hA_lt : (q ^ 2 - 1) ^ 2 < q ^ 4 := by
    simpa only [← pow_mul] using Nat.pow_lt_pow_left
      (by omega : q ^ 2 - 1 < q ^ 2) (by decide : (2 : ℕ) ≠ 0)
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hb := Nat.le_of_dvd hApos
      ((Nat.prime_two.pow_dvd_iff_le_factorization hApos.ne').mpr le_rfl)
    rw [symplectic_rank_two_two_valuation hx ho, Nat.mul_comm 2 _, pow_mul]
    exact (Nat.pow_le_pow_left hb 2).trans_lt hA_lt
  have hd := cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq
  rw [symplectic_rank_two_residual hq] at hd
  by_cases hplus : l ∣ q ^ 2 + 1
  · have hnA := (linear_four_plus_prime_separation hq hl hl2 hlq hplus).1
    have hnA2 : ¬ l ∣ (q ^ 2 - 1) ^ 2 := fun hh => hnA (hl.dvd_of_dvd_pow hh)
    have hb := Nat.le_of_dvd (Nat.succ_pos (q ^ 2))
      (hl.prime.pow_dvd_of_dvd_mul_left _ hnA2 hd)
    have hscale : 4 * q ^ 2 ≤ q ^ 4 := by
      have hm := Nat.mul_le_mul_right (q ^ 2) hq2
      convert hm using 1 <;> ring
    omega
  · exact (Nat.le_of_dvd (pow_pos hApos 2)
      (hl.prime.pow_dvd_of_dvd_mul_right _ hplus hd)).trans_lt hA_lt

/-- Rank three is a linear dimension-three residual in the squared field
parameter, with one additional quadratic minus factor. -/
theorem symplectic_rank_three_residual (q : ℕ) :
    residual (.C 3 q) = (q ^ 2 - 1) * residual (.linear 3 (q ^ 2)) := by
  norm_num [residual, Finset.prod_Icc_succ_top, ← pow_mul]
  ring

/-- In rank three, the stronger linear residual estimate already gives a
bound below q⁸, hence strict dominance by the characteristic contribution q⁹. -/
theorem symplectic_rank_three_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.C 3 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.C 3 q)).factorization l < q ^ 9 := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hq2 : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hnA : q ^ 2 - 1 ≠ 0 := by omega
  have hnR : residual (.linear 3 (q ^ 2)) ≠ 0 := by
    rw [linear_three_residual_factor (by omega : 2 ≤ q ^ 2)]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by omega)
  have hresne : residual (.C 3 q) ≠ 0 := by
    rw [symplectic_rank_three_residual]
    exact mul_ne_zero hnA hnR
  have hupper := cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hresne (dvd_refl _)
  have hRbound := linear_three_residual_cross_contribution_lt
    (by omega : 2 ≤ q ^ 2) hl (fun hd => hlq (hl.dvd_of_dvd_pow hd))
  have hAbound := Nat.le_of_dvd (by omega : 0 < q ^ 2 - 1)
    ((hl.pow_dvd_iff_le_factorization hnA).mpr le_rfl)
  have hresbound : l ^ (residual (.C 3 q)).factorization l < q ^ 8 := by
    rw [symplectic_rank_three_residual, Nat.factorization_mul hnA hnR, Finsupp.add_apply, pow_add]
    calc
      _ < l ^ (q ^ 2 - 1).factorization l * (q ^ 2) ^ 3 :=
        Nat.mul_lt_mul_of_pos_left hRbound (pow_pos hl.pos _)
      _ ≤ q ^ 2 * (q ^ 2) ^ 3 := Nat.mul_le_mul_right _ (hAbound.trans (Nat.sub_le _ _))
      _ = q ^ 8 := by ring
  exact hupper.trans_lt (lt_trans hresbound
    ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide : 8 < 9)))

/-- The identical B₂/C₂ arithmetic formulas share strict dominance. -/
theorem odd_orthogonal_rank_two_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.B 2 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.B 2 q)).factorization l < q ^ 4 := by
  rw [order_B_eq_C]
  exact symplectic_rank_two_cross_contribution_lt hx hl hlq

/-- The identical B₃/C₃ arithmetic formulas share strict dominance. -/
theorem odd_orthogonal_rank_three_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.B 3 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.B 3 q)).factorization l < q ^ 9 := by
  rw [order_B_eq_C]
  exact symplectic_rank_three_cross_contribution_lt hx hl hlq

end Atlas.OrderArithmetic

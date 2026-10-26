import Atlas.OrderArithmetic.SymplecticSmallDominance

namespace Atlas.OrderArithmetic

/-- The complete rank-three even residual already has cross-prime
contribution below q⁸, before central division. -/
theorem symplectic_rank_three_residual_cross_contribution_lt {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (residual (.C 3 q)).factorization l < q ^ 8 := by
  have hq2 : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hnA : q ^ 2 - 1 ≠ 0 := by omega
  have hnR : residual (.linear 3 (q ^ 2)) ≠ 0 := by
    rw [linear_three_residual_factor (by omega : 2 ≤ q ^ 2)]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by omega)) (by omega)) (by omega)
  have hRbound := linear_three_residual_cross_contribution_lt
    (by omega : 2 ≤ q ^ 2) hl (fun hd => hlq (hl.dvd_of_dvd_pow hd))
  have hAbound := Nat.le_of_dvd (by omega : 0 < q ^ 2 - 1)
    ((hl.pow_dvd_iff_le_factorization hnA).mpr le_rfl)
  rw [symplectic_rank_three_residual, Nat.factorization_mul hnA hnR, Finsupp.add_apply, pow_add]
  calc
    _ < l ^ (q ^ 2 - 1).factorization l * (q ^ 2) ^ 3 :=
      Nat.mul_lt_mul_of_pos_left hRbound (pow_pos hl.pos _)
    _ ≤ q ^ 2 * (q ^ 2) ^ 3 := Nat.mul_le_mul_right _ (hAbound.trans (Nat.sub_le _ _))
    _ = q ^ 8 := by ring

/-- The rank-four split orthogonal residual is dominated already before its
central quotient is taken. -/
theorem split_orthogonal_rank_four_residual_cross_contribution_lt {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (residual (.Dplus 4 q)).factorization l < q ^ 12 := by
  have hq4 : 2 ≤ q ^ 4 := hq.trans (by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 1 ≤ 4))
  have hM : q ^ 4 - 1 ≠ 0 := by omega
  have hR : residual (.C 3 q) ≠ 0 := even_minus_segment_ne_zero hq 3
  have he : residual (.Dplus 4 q) = (q ^ 4 - 1) * residual (.C 3 q) := rfl
  have hRbound := symplectic_rank_three_residual_cross_contribution_lt hq hl hlq
  have hMbound := Nat.le_of_dvd (by omega : 0 < q ^ 4 - 1)
    ((hl.pow_dvd_iff_le_factorization hM).mpr le_rfl)
  rw [he, Nat.factorization_mul hM hR, Finsupp.add_apply, pow_add]
  calc
    _ ≤ q ^ 4 * l ^ (residual (.C 3 q)).factorization l :=
      Nat.mul_le_mul_right _ (hMbound.trans (Nat.sub_le _ _))
    _ < q ^ 4 * q ^ 8 := Nat.mul_lt_mul_of_pos_left hRbound (by positivity)
    _ = q ^ 12 := by ring

/-- The rank-four nonsplit extra factor is prime-separated from the rank-three
even residual, except for its single factor of two. -/
theorem minus_orthogonal_rank_four_residual_cross_contribution_lt {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (residual (.Dminus 4 q)).factorization l < q ^ 12 := by
  have hq2 : 4 ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hq4 : 2 ≤ q ^ 4 := hq.trans (by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 1 ≤ 4))
  have hM : q ^ 4 + 1 ≠ 0 := by omega
  have hR : residual (.C 3 q) ≠ 0 := even_minus_segment_ne_zero hq 3
  have he : residual (.Dminus 4 q) = (q ^ 4 + 1) * residual (.C 3 q) := rfl
  have hRbound := symplectic_rank_three_residual_cross_contribution_lt hq hl hlq
  rw [he, Nat.factorization_mul hM hR, Finsupp.add_apply, pow_add]
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hv : (q ^ 4 + 1).factorization 2 = 1 := by
      simpa only [← pow_mul] using linear_four_plus_two_valuation (ho.pow (n := 2))
    rw [hv, pow_one]
    calc
      _ < 2 * q ^ 8 := Nat.mul_lt_mul_of_pos_left hRbound (by decide)
      _ ≤ q * q ^ 8 := Nat.mul_le_mul_right _ hq
      _ = q ^ 9 := by ring
      _ < q ^ 12 := (Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide)
  by_cases hplus : l ∣ q ^ 4 + 1
  · have hpQ : l ∣ (q ^ 2) ^ 2 + 1 := by simpa only [← pow_mul] using hplus
    have hlQ : ¬ l ∣ q ^ 2 := fun hh => hlq (hl.dvd_of_dvd_pow hh)
    obtain ⟨hnminus, hnR3⟩ := linear_four_plus_prime_separation
      (by omega : 2 ≤ q ^ 2) hl hl2 hlQ hpQ
    have hnA : ¬ l ∣ q ^ 2 - 1 := fun hd =>
      hnminus (hd.trans (Nat.sub_one_dvd_pow_sub_one (q ^ 2) 2))
    have hnC3 : ¬ l ∣ residual (.C 3 q) := by
      rw [symplectic_rank_three_residual]
      exact hl.prime.not_dvd_mul hnA hnR3
    rw [Nat.factorization_eq_zero_of_not_dvd hnC3, pow_zero, mul_one]
    have hb := Nat.le_of_dvd (Nat.succ_pos (q ^ 4))
      ((hl.pow_dvd_iff_le_factorization hM).mpr le_rfl)
    have hscale : 2 * q ^ 4 ≤ q ^ 5 := by
      calc
        _ ≤ q * q ^ 4 := Nat.mul_le_mul_right _ hq
        _ = q ^ 5 := by ring
    have hlarge := Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 5 ≤ 12)
    omega
  · rw [Nat.factorization_eq_zero_of_not_dvd hplus, pow_zero, one_mul]
    exact lt_trans hRbound ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide : 8 < 12))

/-- Full cross-characteristic dominance for split orthogonal rank four. -/
theorem split_orthogonal_rank_four_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.Dplus 4 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dplus 4 q)).factorization l < q ^ 12 := by
  have hq : 2 ≤ q := primePower_two_le hx.2
  have hq4 : 2 ≤ q ^ 4 := hq.trans (by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 1 ≤ 4))
  have hn : residual (.Dplus 4 q) ≠ 0 :=
    mul_ne_zero (by omega : q ^ 4 - 1 ≠ 0) (even_minus_segment_ne_zero hq 3)
  exact (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hn (dvd_refl _)).trans_lt
    (split_orthogonal_rank_four_residual_cross_contribution_lt hq hl hlq)

/-- Full cross-characteristic dominance for nonsplit orthogonal rank four. -/
theorem minus_orthogonal_rank_four_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.Dminus 4 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dminus 4 q)).factorization l < q ^ 12 := by
  have hq : 2 ≤ q := primePower_two_le hx.2
  have hn : residual (.Dminus 4 q) ≠ 0 :=
    mul_ne_zero (by omega : q ^ 4 + 1 ≠ 0) (even_minus_segment_ne_zero hq 3)
  exact (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq hn (dvd_refl _)).trans_lt
    (minus_orthogonal_rank_four_residual_cross_contribution_lt hq hl hlq)

end Atlas.OrderArithmetic

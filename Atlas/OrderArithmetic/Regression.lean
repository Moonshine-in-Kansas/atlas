import Atlas.OrderArithmetic.Normalization

namespace Atlas.OrderArithmetic

theorem regression_6048 : order (.unitary 3 3) = 6048 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    unitaryFactor, Finset.prod_Icc_succ_top]

theorem regression_504 : order (.linear 2 8) = 504 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem regression_BC33 : order (.B 3 3) = 4585351680 ∧ order (.C 3 3) = 4585351680 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem regression_A8_exception : normalize (.linear 3 4) ≠ .alternating 8 ∧
    Exceptional (.alternating 8) (.linear 3 4) := by
  constructor
  · simp [normalize]
  · exact Or.inl ⟨rfl, rfl⟩

theorem regression_BC_odd : normalize (.B 3 3) ≠ normalize (.C 3 3) := by
  norm_num [normalize]
  decide

theorem regression_BC_even : normalize (.B 17 (2 ^ 11)) = normalize (.C 17 (2 ^ 11)) := by
  norm_num [normalize]

theorem regression_BC_rank_two (q : ℕ) : normalize (.B 2 q) = normalize (.C 2 q) := by
  simp [normalize]

theorem excluded_small_labels :
    ¬ Admissible (.linear 2 2) ∧ ¬ Admissible (.linear 2 3) ∧
    ¬ Admissible (.unitary 3 2) ∧ ¬ Admissible (.B 2 2) ∧ ¬ Admissible (.C 2 2) ∧
    ¬ Admissible (.G2 2) ∧ ¬ Admissible (.suzuki 2) ∧
    ¬ Admissible (.smallRee 3) ∧ ¬ Admissible (.largeRee 2) := by
  simp only [Admissible]
  norm_num
  refine ⟨?_, ?_, ?_⟩
  all_goals intro m hm h
  · have hp : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hp : 3 ^ 3 ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hp : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem largeRee_binary_twice_tits : order (.largeRee 2) = 2 * order (.fixed .Tits) := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator, fixedOrder]

end Atlas.OrderArithmetic

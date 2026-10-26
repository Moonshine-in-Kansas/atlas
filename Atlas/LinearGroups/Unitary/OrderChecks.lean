import Atlas.LinearGroups.Unitary.Order
import Atlas.LinearGroups.Unitary.ScalarParameters

/-! Small-field specializations of the uniform orders, on actual quadratic extensions. -/
noncomputable section
namespace Atlas.Unitary.OrderChecks

abbrev BinaryExtension := FiniteField.Extension (ZMod 2) 2 2
abbrev TernaryExtension := FiniteField.Extension (ZMod 3) 3 2

theorem binary_degree : Module.finrank (ZMod 2) BinaryExtension = 2 :=
by
  apply Nat.pow_right_injective (show 1 < Nat.card (ZMod 2) from Finite.one_lt_card)
  dsimp only
  rw [← Module.natCard_eq_pow_finrank]
  exact FiniteField.natCard_extension (ZMod 2) 2 2

theorem ternary_degree : Module.finrank (ZMod 3) TernaryExtension = 2 :=
by
  apply Nat.pow_right_injective (show 1 < Nat.card (ZMod 3) from Finite.one_lt_card)
  dsimp only
  rw [← Module.natCard_eq_pow_finrank]
  exact FiniteField.natCard_extension (ZMod 3) 3 2

theorem u_three_binary : Nat.card (U (ZMod 2) BinaryExtension 3 binary_degree) = 648 := by
  rw [card_u binary_degree]
  norm_num [orderU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem su_three_binary : Nat.card (SU (ZMod 2) BinaryExtension 3 binary_degree) = 216 := by
  rw [card_su binary_degree 3 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem su_four_binary : Nat.card (SU (ZMod 2) BinaryExtension 4 binary_degree) = 25920 := by
  rw [card_su binary_degree 4 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem su_five_binary : Nat.card (SU (ZMod 2) BinaryExtension 5 binary_degree) = 13685760 := by
  rw [card_su binary_degree 5 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem su_three_ternary : Nat.card (SU (ZMod 3) TernaryExtension 3 ternary_degree) = 6048 := by
  rw [card_su ternary_degree 3 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem binary_three_scalar_parameters :
    Nat.card (scalarParameters (ZMod 2) BinaryExtension 3) = 3 := by
  rw [card_scalarParameters (ZMod 2) BinaryExtension binary_degree]
  norm_num [Nat.card_zmod]

theorem binary_four_scalar_parameters :
    Nat.card (scalarParameters (ZMod 2) BinaryExtension 4) = 1 := by
  rw [card_scalarParameters (ZMod 2) BinaryExtension binary_degree]
  norm_num [Nat.card_zmod]
end Atlas.Unitary.OrderChecks

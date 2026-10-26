import Atlas.LinearGroups.Unitary.ProjectiveOrder
import Atlas.LinearGroups.Unitary.OrderChecks

/-! Kernel-checked numerical specializations of the uniform projective order.
The carriers are actual quadratic extensions, not groups postulated from their order. -/
noncomputable section
namespace Atlas.Unitary.OrderChecks

theorem psu_two_binary : Nat.card (PSU (ZMod 2) BinaryExtension 2 binary_degree) = 6 := by
  rw [card_psu binary_degree 2 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem psu_two_ternary : Nat.card (PSU (ZMod 3) TernaryExtension 2 ternary_degree) = 12 := by
  rw [card_psu ternary_degree 2 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem psu_three_binary : Nat.card (PSU (ZMod 2) BinaryExtension 3 binary_degree) = 72 := by
  rw [card_psu binary_degree 3 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem psu_three_ternary : Nat.card (PSU (ZMod 3) TernaryExtension 3 ternary_degree) = 6048 := by
  rw [card_psu ternary_degree 3 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem psu_four_binary : Nat.card (PSU (ZMod 2) BinaryExtension 4 binary_degree) = 25920 := by
  rw [card_psu binary_degree 4 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem psu_four_ternary :
    Nat.card (PSU (ZMod 3) TernaryExtension 4 ternary_degree) = 3265920 := by
  rw [card_psu ternary_degree 4 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem psu_five_binary :
    Nat.card (PSU (ZMod 2) BinaryExtension 5 binary_degree) = 13685760 := by
  rw [card_psu binary_degree 5 (by decide)]
  norm_num [orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

theorem center_three_binary :
    Nat.card (Subgroup.center (SU (ZMod 2) BinaryExtension 3 binary_degree)) = 3 := by
  rw [card_center binary_degree (by decide)]
  norm_num [Nat.card_zmod]

theorem center_four_binary :
    Nat.card (Subgroup.center (SU (ZMod 2) BinaryExtension 4 binary_degree)) = 1 := by
  rw [card_center binary_degree (by decide)]
  norm_num [Nat.card_zmod]
end Atlas.Unitary.OrderChecks

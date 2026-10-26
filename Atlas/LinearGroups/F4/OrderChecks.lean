import Atlas.LinearGroups.F4.Order
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum

namespace Atlas.F4.OrderChecks
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem binary_order : Nat.card (Model (ZMod 2)) = 3311126603366400 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem ternary_order : Nat.card (Model (ZMod 3)) = 5734420792816671844761600 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem four_order : Nat.card (Model (GaloisField 2 2)) = 19009825523840945451297669120000 := by
  rw [card_Model,GaloisField.card 2 2 (by decide)]
  norm_num

theorem five_order : Nat.card (Model (ZMod 5)) = 2131486317725501953125000000000000000 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem eight_order : Nat.card (Model (GaloisField 2 3)) = 89916256275114328125813913131505293998004633600 := by
  rw [card_Model,GaloisField.card 2 3 (by decide)]
  norm_num

end Atlas.F4.OrderChecks

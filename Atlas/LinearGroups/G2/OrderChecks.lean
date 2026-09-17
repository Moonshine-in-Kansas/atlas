import Atlas.LinearGroups.G2.Order
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum

namespace Atlas.G2.OrderChecks

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem binary_order : Nat.card (Model (ZMod 2)) = 12096 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem ternary_order : Nat.card (Model (ZMod 3)) = 4245696 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem four_order : Nat.card (Model (GaloisField 2 2)) = 251596800 := by
  rw [card_Model, GaloisField.card 2 2 (by decide)]
  norm_num

theorem five_order : Nat.card (Model (ZMod 5)) = 5859000000 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem eight_order : Nat.card (Model (GaloisField 2 3)) = 4329310519296 := by
  rw [card_Model, GaloisField.card 2 3 (by decide)]
  norm_num

theorem binary_points : Nat.card (SingularPoints (ZMod 2)) = 63 := by
  rw [card_singularPoints]
  norm_num [Nat.card_eq_fintype_card]

theorem ternary_points : Nat.card (SingularPoints (ZMod 3)) = 364 := by
  rw [card_singularPoints]
  norm_num [Nat.card_eq_fintype_card]

theorem four_points : Nat.card (SingularPoints (GaloisField 2 2)) = 1365 := by
  rw [card_singularPoints, GaloisField.card 2 2 (by decide)]
  norm_num

end Atlas.G2.OrderChecks

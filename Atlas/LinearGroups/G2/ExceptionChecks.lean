import Atlas.LinearGroups.G2.BinaryException
import Atlas.LinearGroups.G2.SimplicityChecks

namespace Atlas.G2.ExceptionChecks

theorem binary_not_simple : ¬ IsSimpleGroup (Model (ZMod 2)) :=
  not_simple_binary (by simp [Nat.card_eq_fintype_card])

theorem binary_normal_order : Nat.card (longRootNormalClosure (F := ZMod 2)) = 6048 :=
  card_longRootNormalClosure_binary (by simp [Nat.card_eq_fintype_card])

theorem binary_index : (longRootNormalClosure (F := ZMod 2)).index = 2 :=
  index_longRootNormalClosure_binary (by simp [Nat.card_eq_fintype_card])

theorem binary_exact_range : (IsSimpleGroup (Model (ZMod 2)) ↔ False) := by
  rw [isSimple_iff]
  norm_num [Nat.card_eq_fintype_card]

theorem ternary_exact_range : (IsSimpleGroup (Model (ZMod 3)) ↔ True) := by
  rw [isSimple_iff]
  norm_num [Nat.card_eq_fintype_card]

theorem four_exact_range : (IsSimpleGroup (Model (GaloisField 2 2)) ↔ True) := by
  rw [isSimple_iff,GaloisField.card 2 2 (by decide)]
  norm_num

end Atlas.G2.ExceptionChecks

import Atlas.LinearGroups.G2.Simplicity
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum

namespace Atlas.G2.SimplicityChecks
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem ternary_simple : IsSimpleGroup (Model (ZMod 3)) :=
  isSimple (by norm_num [Nat.card_eq_fintype_card])

theorem four_simple : IsSimpleGroup (Model (GaloisField 2 2)) := by
  apply isSimple
  rw [GaloisField.card 2 2 (by decide)]
  norm_num

theorem five_simple : IsSimpleGroup (Model (ZMod 5)) :=
  isSimple (by norm_num [Nat.card_eq_fintype_card])

theorem eight_simple : IsSimpleGroup (Model (GaloisField 2 3)) := by
  apply isSimple
  rw [GaloisField.card 2 3 (by decide)]
  norm_num

theorem binary_noncommutative : ∃ g h : Model (ZMod 2),g*h ≠ h*g := exists_mul_ne_mul

theorem ternary_noncommutative : ∃ g h : Model (ZMod 3),g*h ≠ h*g := exists_mul_ne_mul
end Atlas.G2.SimplicityChecks

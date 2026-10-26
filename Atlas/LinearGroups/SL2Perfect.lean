import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.IsPerfect

/-! SL₂ perfectness from elementary generation and a diagonal commutator. -/
namespace Atlas
variable {F : Type*} [Field F] [Finite F]

theorem sl_two_perfect_of_four_le_card (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨a,ha⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ) (k := 2) (by decide)
    (by rw [Nat.card_units]; omega)
  have ha' : (a : F)^2 ≠ 1 := fun h => ha (Units.ext (by simpa using h))
  exact ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero a) ha'⟩

end Atlas

import Atlas.Algebra.FiniteFieldSignSquares
import Atlas.Algebra.SquareClasses

noncomputable section
namespace Atlas
variable {F : Type*} [Field F] [Finite F]

theorem squareClass_mul_nonsquare_eq_one_iff (h2 : (2 : F) ≠ 0)
    (a d : Fˣ) (hd : ¬ IsSquare d.val) :
    squareClass F (a*d) = 1 ↔ ¬ ∃ b : Fˣ, b^2=a := by
  have hd1 : squareClass F d ≠ 1 := by
    intro h
    exact hd ((units_square_iff_field_square d).mp ((squareClass_eq_one F d).mp h))
  rw [← squareClass_eq_one F a, map_mul]
  constructor
  · intro h ha
    rw [ha, one_mul] at h
    exact hd1 h
  · intro ha
    have hc : Nat.card (SquareClass F) = 2 := by simp [card_squareClass, h2]
    obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (1 : SquareClass F)).mp hc
    have had : squareClass F a = squareClass F d := (hu _ ha).trans (hu _ hd1).symm
    rw [had, ← map_mul, ← pow_two]
    exact squareClass_square F d

end Atlas

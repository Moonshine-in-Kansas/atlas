import Atlas.Algebra.SquareOneUnits
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

/-! # Intrinsic square classes of a field -/
noncomputable section
open scoped Classical
namespace Atlas
variable (F : Type*) [Field F]

def squareUnits : Subgroup Fˣ := (powMonoidHom 2 : Fˣ →* Fˣ).range
abbrev SquareClass := Fˣ ⧸ squareUnits F

def squareClass : Fˣ →* SquareClass F := QuotientGroup.mk' (squareUnits F)

theorem squareClass_eq_one (a : Fˣ) : squareClass F a = 1 ↔ ∃ b : Fˣ, b^2 = a := by
  change (a : Fˣ ⧸ squareUnits F) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  rfl

@[simp] theorem squareClass_square (a : Fˣ) : squareClass F (a^2) = 1 :=
  (squareClass_eq_one F _).mpr ⟨a, rfl⟩

theorem squareClass_mul_square (a b : Fˣ) : squareClass F (a*b^2) = squareClass F a := by
  rw [map_mul, squareClass_square, mul_one]

theorem squareClass_surjective : Function.Surjective (squareClass F) :=
  QuotientGroup.mk'_surjective _

theorem card_squareClass [Finite F] : Nat.card (SquareClass F) = if (2 : F) = 0 then 1 else 2 := by
  have hker : (powMonoidHom 2 : Fˣ →* Fˣ).ker = rootsOfUnity 2 F := by
    ext a
    exact (mem_rootsOfUnity 2 a).symm
  change (powMonoidHom 2 : Fˣ →* Fˣ).range.index = _
  rw [Subgroup.index_range, hker, card_squareOneUnits]

end Atlas

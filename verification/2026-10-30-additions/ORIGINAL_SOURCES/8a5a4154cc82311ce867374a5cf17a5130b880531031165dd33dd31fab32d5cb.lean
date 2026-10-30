import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Field.ZMod
import Atlas.FieldTheory.FiniteQuadraticExtension

/-! A computable coordinate chart for the actual quadratic extension F9/F3.
All field laws come from mathlib's quadratic algebra; only the three-element
no-root condition is discharged by ordinary kernel reduction. -/
namespace Atlas.Comparisons.G2Binary
abbrev BaseThree := ZMod 3
abbrev FieldNine := QuadraticAlgebra BaseThree (-1) 0

instance fieldNineNoRoot : Fact (∀ r : BaseThree, r^2 ≠ -1 + 0*r) := ⟨by decide⟩
instance fieldNineFintype : Fintype FieldNine :=
  Fintype.ofEquiv (BaseThree × BaseThree) (QuadraticAlgebra.equivProd (-1) 0).symm

theorem fieldNine_degree : Module.finrank BaseThree FieldNine = 2 :=
  QuadraticAlgebra.finrank_eq_two (-1) 0

theorem fieldNine_card : Fintype.card FieldNine = 9 := by decide

def imaginaryUnit : FieldNine := ⟨0,1⟩

theorem imaginaryUnit_square : imaginaryUnit ^ 2 = -1 := by decide

/-- The actual finite-extension conjugation equals the explicit cubic map. -/
theorem fieldNine_conjugation (x : FieldNine) :
    Atlas.FiniteQuadratic.conjugation BaseThree FieldNine x = x^3 := by
  rw [Atlas.FiniteQuadratic.conjugation_apply]
  norm_num [Nat.card_eq_fintype_card]

/-- Integer labels are coordinate pairs, never residues modulo nine. -/
def fieldNineLabel (i : Fin 9) : FieldNine := ⟨((i.val % 3 : ℕ) : BaseThree), ((i.val / 3 : ℕ) : BaseThree)⟩

set_option maxRecDepth 4096 in
theorem fieldNineLabel_bijective : Function.Bijective fieldNineLabel := by decide

end Atlas.Comparisons.G2Binary

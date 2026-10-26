import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs

open scoped BigOperators
universe u

/- Comparator reference only: the goal below is deliberately unproved. -/
theorem AtlasExistenceChevalley.E6 {F : Type u} [Field F] [Finite F]  :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ 36 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 5 - 1) * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 8 - 1) * (Nat.card F ^ 9 - 1) * (Nat.card F ^ 12 - 1)) / Nat.gcd 3 (Nat.card F - 1) ∧ IsSimpleGroup G := by
  sorry

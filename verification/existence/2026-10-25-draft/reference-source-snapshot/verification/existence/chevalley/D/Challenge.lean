import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs

open scoped BigOperators
universe u

/- Comparator reference only: the goal below is deliberately unproved. -/
theorem AtlasExistenceChevalley.D {F : Type u} [Field F] [Finite F] (r : ℕ) (hr : 4 ≤ r) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (r * (r - 1)) * (Nat.card F ^ r - 1) * ∏ i ∈ Finset.range (r - 1), (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 4 (Nat.card F ^ r - 1) ∧ IsSimpleGroup G := by
  sorry

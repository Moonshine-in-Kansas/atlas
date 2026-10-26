import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs

open scoped BigOperators
universe u

/- Comparator reference only: the goal below is deliberately unproved. -/
theorem AtlasExistenceChevalley.A {F : Type u} [Field F] [Finite F] (r : ℕ) (hr : 1 ≤ r)
    (h2 : (r, Nat.card F) ≠ (1, 2)) (h3 : (r, Nat.card F) ≠ (1, 3)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (r * (r + 1) / 2) * ∏ i ∈ Finset.range r, (Nat.card F ^ (i + 2) - 1)) / Nat.gcd (r + 1) (Nat.card F - 1) ∧ IsSimpleGroup G := by
  sorry

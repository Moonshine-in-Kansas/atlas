import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs

open scoped BigOperators
universe u

/- Comparator reference only: the goal below is deliberately unproved. -/
theorem AtlasExistenceChevalley.C {F : Type u} [Field F] [Finite F] (r : ℕ) (hr : 2 ≤ r) (h2 : (r, Nat.card F) ≠ (2, 2)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (r ^ 2) * ∏ i ∈ Finset.range r, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G := by
  sorry

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharP.Defs

open scoped BigOperators
universe u

/- Reference specification only. Deliberate unproved goals are confined here.
   No ATLAS imports, constructions, assumptions or definition holes.
   Solution.lean must never import this module. -/

theorem AtlasExistence.typeB {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : 1 ≤ n ∧ 2 ≤ Nat.card F ∧ (n, Nat.card F) ≠ (1, 2) ∧
      (n, Nat.card F) ≠ (1, 3) ∧ (n, Nat.card F) ≠ (2, 2)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry


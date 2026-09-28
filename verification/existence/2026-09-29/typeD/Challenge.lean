import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharP.Defs

open scoped BigOperators
universe u

/- Reference specification only. Deliberate unproved goals are confined here.
   No ATLAS imports, constructions, assumptions or definition holes.
   Solution.lean must never import this module. -/

theorem AtlasExistence.typeD {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 4 ≤ n) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1)) * (Nat.card F ^ n - 1) *
      ∏ i ∈ Finset.range (n - 1), (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 4 (Nat.card F ^ n - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry


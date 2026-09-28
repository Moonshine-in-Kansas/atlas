import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharP.Defs

open scoped BigOperators
universe u

/- Reference specification only. Deliberate unproved goals are confined here.
   No ATLAS imports, constructions, assumptions or definition holes.
   Solution.lean must never import this module. -/

theorem AtlasExistence.ReeG2 {F : Type u} [Field F] [Finite F] [CharP F 3] (m : ℕ) (hm : 1 ≤ m)
    (hq : Nat.card F = 3 ^ (2 * m + 1)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 3 * (Nat.card F ^ 3 + 1) * (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry


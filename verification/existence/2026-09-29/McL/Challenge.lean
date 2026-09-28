import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharP.Defs

open scoped BigOperators
universe u

/- Reference specification only. Deliberate unproved goals are confined here.
   No ATLAS imports, constructions, assumptions or definition holes.
   Solution.lean must never import this module. -/

theorem AtlasExistence.McL  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 898128000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry


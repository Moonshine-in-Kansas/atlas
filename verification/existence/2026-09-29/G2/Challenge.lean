import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharP.Defs

open scoped BigOperators
universe u

/- Reference specification only. Deliberate unproved goals are confined here.
   No ATLAS imports, constructions, assumptions or definition holes.
   Solution.lean must never import this module. -/

theorem AtlasExistence.G2 {F : Type u} [Field F] [Finite F] (hq : 2 < Nat.card F) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry


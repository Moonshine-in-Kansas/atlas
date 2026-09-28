import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharP.Defs

open scoped BigOperators
universe u

/- Reference specification only. Deliberate unproved goals are confined here.
   No ATLAS imports, constructions, assumptions or definition holes.
   Solution.lean must never import this module. -/

theorem AtlasExistence.cyclic (p : ℕ) (hp : p.Prime) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = p ∧ IsSimpleGroup G ∧ IsMulCommutative G := by
  sorry

theorem AtlasExistence.alternating (n : ℕ) (hn : 5 ≤ n) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = n.factorial / 2 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.typeA {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (h2 : (n, Nat.card F) ≠ (2, 2)) (h3 : (n, Nat.card F) ≠ (2, 3)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Nat.card F ^ i - 1)) / Nat.gcd n (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.typeB {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : 1 ≤ n ∧ 2 ≤ Nat.card F ∧ (n, Nat.card F) ≠ (1, 2) ∧
      (n, Nat.card F) ≠ (1, 3) ∧ (n, Nat.card F) ≠ (2, 2)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.typeC {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : (n = 1 ∧ 3 < Nat.card F) ∨ (2 ≤ n ∧ (n, Nat.card F) ≠ (2, 2))) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.typeD {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 4 ≤ n) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * (n - 1)) * (Nat.card F ^ n - 1) *
      ∏ i ∈ Finset.range (n - 1), (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 4 (Nat.card F ^ n - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.G2 {F : Type u} [Field F] [Finite F] (hq : 2 < Nat.card F) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.ReeG2 {F : Type u} [Field F] [Finite F] [CharP F 3] (m : ℕ) (hm : 1 ≤ m)
    (hq : Nat.card F = 3 ^ (2 * m + 1)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F ^ 3 * (Nat.card F ^ 3 + 1) * (Nat.card F - 1) ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.M11  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 7920 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.M12  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 95040 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.M22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 443520 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.M23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 10200960 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.M24  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 244823040 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.Co1  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4157776806543360000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.Co2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 42305421312000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.Co3  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 495766656000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.McL  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 898128000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.HS  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 44352000 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.Suz  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 448345497600 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.J2  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 604800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.Fi22  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 64561751654400 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.Fi23  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 4089470473293004800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry

theorem AtlasExistence.Fi24Prime  :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = 1255205709190661721292800 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G := by
  sorry


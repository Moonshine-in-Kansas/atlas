import Atlas.LinearGroups.TypeC
import Atlas.LinearGroups.Symplectic.ProjectiveInvolutionCount
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
universe u

/-- Number of conjugacy classes containing an element of order exactly two. -/
noncomputable def AtlasExistenceInvariant.k2 (G : Type*) [Group G] : ℕ :=
  Nat.card {c : ConjClasses G // ∃ g : G, ConjClasses.mk g = c ∧ orderOf g = 2}

private theorem not_comm_of_pair {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro ⟨⟨hc⟩⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (hc a b)

theorem AtlasDistinguished.typeC {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : (n = 1 ∧ 3 < Nat.card F) ∨ (2 ≤ n ∧ (n, Nat.card F) ≠ (2, 2))) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧
    IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
    ((2 : F) ≠ 0 → AtlasExistenceInvariant.k2 G = n / 2 + 1) := by
  have hn : 0 < n := by rcases h with h | h <;> omega
  refine ⟨Atlas.Symplectic.PSp n F, inferInstance, inferInstance,
    Atlas.Symplectic.card_psp hn, Atlas.Symplectic.simple_of_good h,
    Atlas.Symplectic.projective_not_commutative h, ?_⟩
  intro h2
  exact Atlas.Symplectic.k2_psp hn h2


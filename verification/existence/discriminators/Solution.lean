import Atlas.LinearGroups.Orthogonal.BAllRanksConstruction
import Atlas.LinearGroups.TypeC
import Atlas.Comparisons.Classical.OrthogonalInvolutions
import Atlas.Comparisons.Exceptional.Order20160Nonisomorphism
import Atlas.Families.Alternating.Basic
import Atlas.LinearGroups.TypeA
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

theorem AtlasDistinguished.typeB {F : Type u} [Field F] [Finite F] (n : ℕ)
    (h : 1 ≤ n ∧ 2 ≤ Nat.card F ∧ (n, Nat.card F) ≠ (1, 2) ∧
      (n, Nat.card F) ≠ (1, 3) ∧ (n, Nat.card F) ≠ (2, 2)) :
  ∃ (G : Type u) (_ : Group G), Finite G ∧
    Nat.card G = (Nat.card F ^ (n * n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2 * (i + 1)) - 1)) / Nat.gcd 2 (Nat.card F - 1) ∧
    IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
    ((2 : F) ≠ 0 → AtlasExistenceInvariant.k2 G = n) := by
  refine ⟨Atlas.Orthogonal.B n F, inferInstance, inferInstance,
    Atlas.Orthogonal.B_card_all_rank n h.1,
    Atlas.Orthogonal.B_simple_all_rank n h,
    Atlas.Orthogonal.B_noncommutative_all_rank n h, ?_⟩
  intro h2
  exact Atlas.Orthogonal.B_k2 n h.1 h2

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

theorem AtlasDistinguished.alternating8 :
  ∃ (G : Type) (_ : Group G), Finite G ∧
    Nat.card G = 20160 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
    ∀ P : Sylow 2 G, Nat.card (Subgroup.center P) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  refine ⟨alternatingGroup (Fin 8), inferInstance, inferInstance,
    Atlas.Comparisons.Exceptional.alt8_card,
    Atlas.Families.Alternating.isSimpleGroup 8 (by change 5 ≤ 8; decide),
    not_comm_of_pair (Atlas.Families.Alternating.exists_mul_ne_mul 8 (by decide)), ?_⟩
  intro P
  let Q := Atlas.LinearGroups.UnitriangularFour.sylowTwo (ZMod 2) (by simp)
  have h := Atlas.GroupTheory.sylow_center_card_eq_of_mulEquiv
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm P Q
  exact h.trans (Atlas.LinearGroups.UnitriangularFour.sylowTwo_center_card (ZMod 2) (by simp))

theorem AtlasDistinguished.psl3Four :
  ∃ (G : Type) (_ : Group G), Finite G ∧
    Nat.card G = 20160 ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
    ∀ P : Sylow 2 G, Nat.card (Subgroup.center P) = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let F := GaloisField 2 2
  have hF : Nat.card F = 4 := by simpa [F] using GaloisField.card 2 2 (by decide)
  have h := Atlas.typeA_construction (F := F) 3 (by decide) (by simp) (by simp)
  refine ⟨Matrix.ProjectiveSpecialLinearGroup (Fin 3) F, inferInstance, inferInstance,
    Atlas.LinearGroups.UnitriangularThree.psl3_card_four F hF, h.simple, h.nonabelian, ?_⟩
  intro P
  let Q := Atlas.LinearGroups.UnitriangularThree.sylowTwo F hF
  have hc := Atlas.GroupTheory.sylow_center_card_eq_of_mulEquiv (MulEquiv.refl _) P Q
  exact hc.trans (Atlas.LinearGroups.UnitriangularThree.sylowTwo_center_card F hF)


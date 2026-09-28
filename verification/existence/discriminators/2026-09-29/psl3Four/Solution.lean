import Atlas.LinearGroups.TypeA
import Atlas.LinearGroups.UnitriangularThreeProjective
import Atlas.GroupTheory.SylowCenterInvariant
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


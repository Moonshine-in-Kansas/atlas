import Atlas.Families.Alternating.Basic
import Atlas.Comparisons.Exceptional.Order20160A8
import Atlas.LinearGroups.UnitriangularFourProjective
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


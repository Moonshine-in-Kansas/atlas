import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.SetTheory.Cardinal.Finite

/-! # Faithful doubly transitive actions of degree at least three have trivial center -/
namespace Atlas
variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
  [MulAction.IsMultiplyPretransitive G X 2] [Finite X]

theorem center_eq_bot_of_two_transitive (hc : 3 ≤ Nat.card X) : Subgroup.center G = ⊥ := by
  classical
  letI := Fintype.ofFinite X
  apply bot_unique
  intro g hg
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := X)
  intro x
  rw [one_smul]
  by_contra h
  obtain ⟨y, hyx, hyg⟩ : ∃ y : X, y ≠ x ∧ y ≠ g • x := by
    by_contra! hn
    have hs : (Finset.univ : Finset X) ⊆ {x,g • x} := by
      intro y _
      by_cases hy : y = x
      · simp [hy]
      · simp [hn y hy]
    have hcard := Finset.card_le_card hs
    have hpair := Finset.card_insert_le x ({g • x} : Finset X)
    simp only [Finset.card_univ, Finset.card_singleton] at hcard hpair
    rw [Nat.card_eq_fintype_card] at hc
    omega
  obtain ⟨k,hkx,hky⟩ := (MulAction.is_two_pretransitive_iff.mp
    (inferInstance : MulAction.IsMultiplyPretransitive G X 2)) (Ne.symm h) (Ne.symm hyx)
  have he : k • (g • x) = g • x := by
    rw [← mul_smul, (Subgroup.mem_center_iff.mp hg k), mul_smul, hkx]
  exact hyg (hky.symm.trans he)
end Atlas

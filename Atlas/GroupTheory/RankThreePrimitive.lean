import Mathlib.GroupTheory.GroupAction.Primitive

/-! # Primitivity from two stabilizer orbits and geometric connectors -/
noncomputable section
namespace Atlas.GroupTheory
open MulAction
open scoped Pointwise
variable {G X : Type*} [Group G] [MulAction G X]

/-- A block containing a base contains each point-stabilizer orbit that it meets. -/
theorem block_contains_stabilizer_transport {B : Set X} (hB : IsBlock G B)
    {a x y : X} (ha : a ∈ B) (hx : x ∈ B)
    (hxy : ∃ g : stabilizer G a, g • x = y) : y ∈ B := by
  obtain ⟨g, hg⟩ := hxy
  have hfix : g.val • B = B := hB.stabilizer_le ha g.prop
  rw [← hg]
  change g.val • x ∈ B
  rw [← hfix, Set.smul_mem_smul_set_iff]
  exact hx

/-- A geometric rank-three criterion, with no counting assumptions.

The related suborbit omits the base explicitly, so a reflexive orthogonality relation
is allowed. Two nonrelated points have a distinct common related connector; two
distinct related points have a common nonrelated connector. Together with the two
explicit stabilizer-transitivity assertions, these connectors force every nonsingleton
block to be the whole space. No independent invariance or reflexivity assumption is
needed: the concrete orbit assertions are sufficient. -/
theorem primitive_of_two_suborbits_and_connectors [IsPretransitive G X]
    (a : X) (R : X → X → Prop) (hSymm : Symmetric R)
    (hRelated : ∀ x y z, y ≠ x → z ≠ x → R x y → R x z →
      ∃ g : stabilizer G x, g • y = z)
    (hNonrelated : ∀ x y z, ¬ R x y → ¬ R x z →
      ∃ g : stabilizer G x, g • y = z)
    (hRelatedConnector : ∀ x y, x ≠ y → ¬ R x y →
      ∃ z, z ≠ x ∧ z ≠ y ∧ R x z ∧ R y z)
    (hNonrelatedConnector : ∀ x y, x ≠ y → R x y →
      ∃ z, ¬ R x z ∧ ¬ R y z) :
    IsPreprimitive G X := by
  classical
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  by_cases hs : ∀ x ∈ B, x = a
  · left
    intro x hx y hy
    exact (hs x hx).trans (hs y hy).symm
  · push_neg at hs
    obtain ⟨b, hb, hba⟩ := hs
    right
    apply Set.eq_univ_of_forall
    intro r
    by_cases hra : r = a
    · simpa only [hra] using ha
    by_cases hab : R a b
    · have hRelatedMem (x : X) (hxa : x ≠ a) (hax : R a x) : x ∈ B :=
        block_contains_stabilizer_transport hB ha hb (hRelated a b x hba hxa hab hax)
      by_cases har : R a r
      · exact hRelatedMem r hra har
      · obtain ⟨q, hqa, hqr, haq, hrq⟩ :=
          hRelatedConnector a r (Ne.symm hra) har
        have hq : q ∈ B := hRelatedMem q hqa haq
        exact block_contains_stabilizer_transport hB hq ha
          (hRelated q a r (Ne.symm hqa) (Ne.symm hqr) (hSymm haq) (hSymm hrq))
    · have hNonrelatedMem (x : X) (hax : ¬ R a x) : x ∈ B :=
        block_contains_stabilizer_transport hB ha hb (hNonrelated a b x hab hax)
      by_cases har : R a r
      · obtain ⟨q, haq, hrq⟩ := hNonrelatedConnector a r (Ne.symm hra) har
        have hq : q ∈ B := hNonrelatedMem q haq
        exact block_contains_stabilizer_transport hB hq ha
          (hNonrelated q a r (fun h => haq (hSymm h)) (fun h => hrq (hSymm h)))
      · exact hNonrelatedMem r har
end Atlas.GroupTheory

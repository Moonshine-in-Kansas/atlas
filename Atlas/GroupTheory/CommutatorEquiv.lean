import Mathlib.GroupTheory.Commutator.Basic

/-! # Restricting group isomorphisms to their actual derived subgroups -/
noncomputable section
namespace Atlas.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- An isomorphism sends the actual derived subgroup onto the derived subgroup. -/
theorem commutator_map_equiv (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [map_commutator_eq, e.toMonoidHom.range_eq_top.mpr e.surjective, commutator_def]

/-- Restriction of a group isomorphism to its actual derived subgroups. -/
def commutatorEquiv (e : G ≃* H) : commutator G ≃* commutator H :=
  ((commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (commutator_map_equiv e))

@[simp] theorem commutatorEquiv_coe (e : G ≃* H) (g : commutator G) :
    (commutatorEquiv e g : H) = e (g : G) := rfl
end Atlas.GroupTheory

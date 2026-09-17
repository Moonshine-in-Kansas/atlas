import Mathlib.GroupTheory.GroupAction.Blocks

noncomputable section
namespace Atlas.GroupTheory

/-- A normal-subgroup orbit has cardinality dividing the containing full orbit.
The argument restricts to the transitive full orbit and uses the block theorem. -/
theorem normal_orbit_card_dvd {H X : Type*} [Group H] [MulAction H X]
    (P : Subgroup H) [P.Normal] (x : X) :
    Nat.card (MulAction.orbit P x) ∣ Nat.card (MulAction.orbit H x) := by
  let y : MulAction.orbit H x := ⟨x,MulAction.mem_orbit_self x⟩
  let e : MulAction.orbit P y ≃ MulAction.orbit P x :=
    { toFun := fun z => ⟨z.val.val,MulAction.mem_subgroup_orbit_iff.mp z.property⟩
      invFun := fun z => ⟨⟨z.val,MulAction.orbit_subgroup_subset P x z.property⟩,
        MulAction.mem_subgroup_orbit_iff.mpr z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := (MulAction.IsBlock.orbit_of_normal (G := H) (N := P) y).ncard_dvd_card
    ⟨y,MulAction.mem_orbit_self y⟩
  change Nat.card (MulAction.orbit P y) ∣ Nat.card (MulAction.orbit H x) at h
  rwa [Nat.card_congr e] at h

end Atlas.GroupTheory

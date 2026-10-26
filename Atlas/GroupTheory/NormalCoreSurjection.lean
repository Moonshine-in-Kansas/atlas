import Mathlib.GroupTheory.GroupAction.Quotient

/-! Normal cores and faithful coset actions under an actual surjective group map.
This infrastructure has no finite-group or Chevalley hypothesis. -/
namespace Atlas.GroupTheory

theorem normalCore_map_of_surjective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (H : Subgroup G)
    (hker : f.ker ≤ H) :
    (H.map f).normalCore = H.normalCore.map f := by
  letI : (H.normalCore.map f).Normal := Subgroup.Normal.map inferInstance f hf
  apply le_antisymm
  · have hcomap : (H.map f).normalCore.comap f ≤ H.normalCore := by
      apply Subgroup.normal_le_normalCore.mpr
      calc
        (H.map f).normalCore.comap f ≤ (H.map f).comap f :=
          Subgroup.comap_mono (H.map f).normalCore_le
        _ = H := Subgroup.comap_map_eq_self hker
    have hm := Subgroup.map_mono (f := f) hcomap
    rwa [Subgroup.map_comap_eq_self_of_surjective hf] at hm
  · exact Subgroup.normal_le_normalCore.mpr (Subgroup.map_mono H.normalCore_le)

/-- If a subgroup's full core is precisely the projection kernel, its image
has a faithful coset action. No simplicity or transitivity of normal subgroups
is hidden in this statement. -/
theorem cosetAction_injective_of_normalCore_eq_ker
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (H : Subgroup G)
    (hcore : H.normalCore = f.ker) :
    Function.Injective (MulAction.toPermHom Q (Q ⧸ H.map f)) := by
  apply (MulAction.toPermHom Q (Q ⧸ H.map f)).ker_eq_bot_iff.mp
  rw [← Subgroup.normalCore_eq_ker,
    normalCore_map_of_surjective f hf H (hcore ▸ H.normalCore_le),
    hcore, Subgroup.map_ker_self]

end Atlas.GroupTheory

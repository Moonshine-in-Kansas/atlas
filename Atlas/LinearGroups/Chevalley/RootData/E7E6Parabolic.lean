import Atlas.LinearGroups.Chevalley.RootData.E7E6RootEmbedding
import Atlas.LinearGroups.Chevalley.RootData.E7WeightParabolic
import Atlas.LinearGroups.Chevalley.RootData.ParabolicRootRestriction
import Atlas.LinearGroups.Chevalley.RootData.ParabolicWeylEmbedding

/-! The actual E6 Weyl image is the first-six-node E7 parabolic, with equality
of intrinsic and ambient word length. No Weyl or group order is used. -/
noncomputable section
set_option maxRecDepth 32768
namespace Atlas.Chevalley.E7E6
open Classical RootData
local instance : Fintype E6Data.Root := Fintype.ofFinite E6Data.Root
private abbrev P := E6Data.pairing
private abbrev b := E6Data.base
private abbrev Q := E7Data.pairing
private abbrev c := E7Data.base

theorem mem_J_iff_simpleEmbedding (j : c.support) :
    j ∈ E7WeightOrbit.J ↔ ∃ i : b.support, simpleEmbedding i = j := by
  obtain ⟨a, rfl⟩ := E7Data.baseIndexEquiv.surjective j
  have hnodes : ∀ a : Fin 7, a ≠ 6 ↔ ∃ d : Fin 6, nodeEmbedding d = a := by decide
  simp only [E7WeightOrbit.J, Finset.mem_erase, Finset.mem_univ, and_true]
  simp only [E7Data.baseIndexEquiv.injective.ne_iff]
  constructor
  · intro ha
    obtain ⟨d, hd⟩ := (hnodes a).mp ha
    refine ⟨E6Data.baseIndexEquiv d, ?_⟩
    change E7Data.baseIndexEquiv
      (nodeEmbedding (E6Data.baseIndexEquiv.symm (E6Data.baseIndexEquiv d))) =
        E7Data.baseIndexEquiv a
    rw [Equiv.symm_apply_apply, hd]
  · rintro ⟨i, hi⟩
    obtain ⟨d, rfl⟩ := E6Data.baseIndexEquiv.surjective i
    have hd : nodeEmbedding d = a := by
      apply E7Data.baseIndexEquiv.injective
      change E7Data.baseIndexEquiv
        (nodeEmbedding (E6Data.baseIndexEquiv.symm (E6Data.baseIndexEquiv d))) =
          E7Data.baseIndexEquiv a at hi
      simpa only [Equiv.symm_apply_apply] using hi
    exact (hnodes a).mpr ⟨d, hd⟩

/-- Equivalence of the literal actual E6 Weyl image and the actual E7 parabolic. -/
def parabolicEquiv :
    P.weylGroupToPerm.range ≃* rootParabolicSubgroup Q c E7WeightOrbit.J :=
  (rootParabolicRestrictionEquiv P b Q c rootEmbedding simpleEmbedding
    E7WeightOrbit.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple
    rootEmbedding_simple).symm

def weylEmbedding : P.weylGroupToPerm.range →* Q.weylGroupToPerm.range :=
  (rootParabolicSubgroup Q c E7WeightOrbit.J).subtype.comp parabolicEquiv.toMonoidHom

theorem weylEmbedding_injective : Function.Injective weylEmbedding :=
  Subtype.val_injective.comp parabolicEquiv.injective

theorem weylEmbedding_simple (i : b.support) :
    weylEmbedding (simpleWeylReflection P b i) =
      simpleWeylReflection Q c (simpleEmbedding i) := by
  let s : rootParabolicSubgroup Q c E7WeightOrbit.J :=
    ⟨simpleWeylReflection Q c (simpleEmbedding i),
      Subgroup.subset_closure ⟨simpleEmbedding i,
        (mem_J_iff_simpleEmbedding _).mpr ⟨i, rfl⟩, rfl⟩⟩
  have hs : parabolicEquiv (simpleWeylReflection P b i) = s := by
    apply parabolicEquiv.symm.injective
    rw [MulEquiv.symm_apply_apply]
    change simpleWeylReflection P b i =
      rootParabolicRestriction P b Q c rootEmbedding simpleEmbedding
        E7WeightOrbit.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple s
    exact (rootParabolicRestriction_simple P b Q c rootEmbedding simpleEmbedding
      E7WeightOrbit.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple i).symm
  change (parabolicEquiv (simpleWeylReflection P b i)).val = s.val
  rw [hs]

theorem weylEmbedding_range :
    weylEmbedding.range = rootParabolicSubgroup Q c E7WeightOrbit.J :=
  rootWeylHom_range_eq_parabolic P b Q c weylEmbedding simpleEmbedding
    weylEmbedding_simple E7WeightOrbit.J mem_J_iff_simpleEmbedding

theorem weylEmbedding_length (w : P.weylGroupToPerm.range) :
    rootWeylLength Q c (weylEmbedding w) = rootWeylLength P b w :=
  rootWeylHom_length P b Q c weylEmbedding simpleEmbedding weylEmbedding_simple
    weylEmbedding_injective E7WeightOrbit.J mem_J_iff_simpleEmbedding w

theorem parabolicEquiv_length (w : P.weylGroupToPerm.range) :
    rootWeylLength Q c (parabolicEquiv w).val = rootWeylLength P b w :=
  weylEmbedding_length w

end Atlas.Chevalley.E7E6

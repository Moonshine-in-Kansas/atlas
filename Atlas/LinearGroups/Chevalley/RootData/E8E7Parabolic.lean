import Atlas.LinearGroups.Chevalley.RootData.E8E7RootEmbedding
import Atlas.LinearGroups.Chevalley.RootData.E8RootParabolic
import Atlas.LinearGroups.Chevalley.RootData.ParabolicRootRestriction
import Atlas.LinearGroups.Chevalley.RootData.ParabolicWeylEmbedding

/-! The actual E7 Weyl image is the node-seven-omitted E8 parabolic,
with equality of intrinsic and ambient minimum word length. -/
noncomputable section
set_option maxRecDepth 32768
namespace Atlas.Chevalley.E8E7
open Classical RootData

private abbrev DP := E7Data.pairing
private abbrev db := E7Data.base
private abbrev Q := E8Data.pairing
private abbrev qb := E8Data.base

theorem mem_J_iff_simpleEmbedding (j : qb.support) :
    j ∈ E8Parabolic.J ↔ ∃ i : db.support, simpleEmbedding i = j := by
  obtain ⟨a, rfl⟩ := E8Data.baseIndexEquiv.surjective j
  have hnodes : ∀ a : Fin 8, a ≠ 7 ↔ ∃ d : Fin 7, nodeEmbedding d = a := by decide
  simp only [E8Parabolic.J, Finset.mem_erase, Finset.mem_univ, and_true]
  simp only [E8Data.baseIndexEquiv.injective.ne_iff]
  constructor
  · intro ha
    obtain ⟨d, hd⟩ := (hnodes a).mp ha
    refine ⟨E7Data.baseIndexEquiv d, ?_⟩
    change E8Data.baseIndexEquiv
      (nodeEmbedding ((E7Data.baseIndexEquiv).symm
        (E7Data.baseIndexEquiv d))) = E8Data.baseIndexEquiv a
    rw [Equiv.symm_apply_apply, hd]
  · rintro ⟨i, hi⟩
    obtain ⟨d, rfl⟩ := (E7Data.baseIndexEquiv).surjective i
    have hd : nodeEmbedding d = a := by
      apply E8Data.baseIndexEquiv.injective
      change E8Data.baseIndexEquiv
        (nodeEmbedding ((E7Data.baseIndexEquiv).symm
          (E7Data.baseIndexEquiv d))) = E8Data.baseIndexEquiv a at hi
      simpa only [Equiv.symm_apply_apply] using hi
    exact (hnodes a).mpr ⟨d, hd⟩

/-- An equivalence of literal actual Weyl groups and the literal E8 parabolic. -/
def parabolicEquiv :
    DP.weylGroupToPerm.range ≃* rootParabolicSubgroup Q qb E8Parabolic.J :=
  (rootParabolicRestrictionEquiv DP db Q qb rootEmbedding simpleEmbedding
    E8Parabolic.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple
    rootEmbedding_simple).symm

/-- The corresponding actual ambient Weyl homomorphism. -/
def weylEmbedding : DP.weylGroupToPerm.range →* Q.weylGroupToPerm.range :=
  (rootParabolicSubgroup Q qb E8Parabolic.J).subtype.comp parabolicEquiv.toMonoidHom

theorem weylEmbedding_injective : Function.Injective weylEmbedding :=
  Subtype.val_injective.comp parabolicEquiv.injective

theorem weylEmbedding_simple (i : db.support) :
    weylEmbedding (simpleWeylReflection DP db i) =
      simpleWeylReflection Q qb (simpleEmbedding i) := by
  let s : rootParabolicSubgroup Q qb E8Parabolic.J :=
    ⟨simpleWeylReflection Q qb (simpleEmbedding i),
      Subgroup.subset_closure ⟨simpleEmbedding i,
        (mem_J_iff_simpleEmbedding _).mpr ⟨i, rfl⟩, rfl⟩⟩
  have hs : parabolicEquiv (simpleWeylReflection DP db i) = s := by
    apply parabolicEquiv.symm.injective
    rw [MulEquiv.symm_apply_apply]
    change simpleWeylReflection DP db i =
      rootParabolicRestriction DP db Q qb rootEmbedding simpleEmbedding
        E8Parabolic.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple s
    exact (rootParabolicRestriction_simple DP db Q qb rootEmbedding simpleEmbedding
      E8Parabolic.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple i).symm
  change (parabolicEquiv (simpleWeylReflection DP db i)).val = s.val
  rw [hs]

theorem weylEmbedding_range :
    weylEmbedding.range = rootParabolicSubgroup Q qb E8Parabolic.J :=
  rootWeylHom_range_eq_parabolic DP db Q qb weylEmbedding simpleEmbedding
    weylEmbedding_simple E8Parabolic.J mem_J_iff_simpleEmbedding

theorem weylEmbedding_length (w : DP.weylGroupToPerm.range) :
    rootWeylLength Q qb (weylEmbedding w) = rootWeylLength DP db w :=
  rootWeylHom_length DP db Q qb weylEmbedding simpleEmbedding weylEmbedding_simple
    weylEmbedding_injective E8Parabolic.J mem_J_iff_simpleEmbedding w

theorem parabolicEquiv_length (w : DP.weylGroupToPerm.range) :
    rootWeylLength Q qb (parabolicEquiv w).val = rootWeylLength DP db w :=
  weylEmbedding_length w

end Atlas.Chevalley.E8E7

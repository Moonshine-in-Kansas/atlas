import Atlas.LinearGroups.Chevalley.RootData.E6D5RootEmbedding
import Atlas.LinearGroups.Chevalley.RootData.E6ParabolicFunctional
import Atlas.LinearGroups.Chevalley.RootData.ParabolicRootRestriction
import Atlas.LinearGroups.Chevalley.RootData.ParabolicWeylEmbedding

/-! The actual D5 Weyl image is the first-node-omitted E6 parabolic,
with equality of intrinsic and ambient minimum word length. -/
noncomputable section
namespace Atlas.Chevalley.E6D5
open Classical RootData

local instance : Fintype E6Data.Root := Fintype.ofFinite E6Data.Root
private abbrev DP := ClassicalData.pairingD 5
private abbrev db := ClassicalData.baseD 3
private abbrev Q := E6Data.pairing
private abbrev qb := E6Data.base

theorem mem_J_iff_simpleEmbedding (j : qb.support) :
    j ∈ E6Parabolic.J ↔ ∃ i : db.support, simpleEmbedding i = j := by
  obtain ⟨a, rfl⟩ := E6Data.baseIndexEquiv.surjective j
  have hnodes : ∀ a : Fin 6, a ≠ 0 ↔ ∃ d : Fin 5, nodeEmbedding d = a := by decide
  simp only [E6Parabolic.J, Finset.mem_erase, Finset.mem_univ, and_true]
  simp only [E6Data.baseIndexEquiv.injective.ne_iff]
  constructor
  · intro ha
    obtain ⟨d, hd⟩ := (hnodes a).mp ha
    refine ⟨ClassicalData.baseDIndexEquiv 3 d, ?_⟩
    change E6Data.baseIndexEquiv
      (nodeEmbedding ((ClassicalData.baseDIndexEquiv 3).symm
        (ClassicalData.baseDIndexEquiv 3 d))) = E6Data.baseIndexEquiv a
    rw [Equiv.symm_apply_apply, hd]
  · rintro ⟨i, hi⟩
    obtain ⟨d, rfl⟩ := (ClassicalData.baseDIndexEquiv 3).surjective i
    have hd : nodeEmbedding d = a := by
      apply E6Data.baseIndexEquiv.injective
      change E6Data.baseIndexEquiv
        (nodeEmbedding ((ClassicalData.baseDIndexEquiv 3).symm
          (ClassicalData.baseDIndexEquiv 3 d))) = E6Data.baseIndexEquiv a at hi
      simpa only [Equiv.symm_apply_apply] using hi
    exact (hnodes a).mpr ⟨d, hd⟩

/-- An equivalence of literal actual Weyl groups and the literal E6 parabolic. -/
def parabolicEquiv :
    DP.weylGroupToPerm.range ≃* rootParabolicSubgroup Q qb E6Parabolic.J :=
  (rootParabolicRestrictionEquiv DP db Q qb rootEmbedding simpleEmbedding
    E6Parabolic.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple
    rootEmbedding_simple).symm

/-- The corresponding actual ambient Weyl homomorphism. -/
def weylEmbedding : DP.weylGroupToPerm.range →* Q.weylGroupToPerm.range :=
  (rootParabolicSubgroup Q qb E6Parabolic.J).subtype.comp parabolicEquiv.toMonoidHom

theorem weylEmbedding_injective : Function.Injective weylEmbedding :=
  Subtype.val_injective.comp parabolicEquiv.injective

theorem weylEmbedding_simple (i : db.support) :
    weylEmbedding (simpleWeylReflection DP db i) =
      simpleWeylReflection Q qb (simpleEmbedding i) := by
  let s : rootParabolicSubgroup Q qb E6Parabolic.J :=
    ⟨simpleWeylReflection Q qb (simpleEmbedding i),
      Subgroup.subset_closure ⟨simpleEmbedding i,
        (mem_J_iff_simpleEmbedding _).mpr ⟨i, rfl⟩, rfl⟩⟩
  have hs : parabolicEquiv (simpleWeylReflection DP db i) = s := by
    apply parabolicEquiv.symm.injective
    rw [MulEquiv.symm_apply_apply]
    change simpleWeylReflection DP db i =
      rootParabolicRestriction DP db Q qb rootEmbedding simpleEmbedding
        E6Parabolic.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple s
    exact (rootParabolicRestriction_simple DP db Q qb rootEmbedding simpleEmbedding
      E6Parabolic.J mem_J_iff_simpleEmbedding rootEmbedding_reflection_simple i).symm
  change (parabolicEquiv (simpleWeylReflection DP db i)).val = s.val
  rw [hs]

theorem weylEmbedding_range :
    weylEmbedding.range = rootParabolicSubgroup Q qb E6Parabolic.J :=
  rootWeylHom_range_eq_parabolic DP db Q qb weylEmbedding simpleEmbedding
    weylEmbedding_simple E6Parabolic.J mem_J_iff_simpleEmbedding

theorem weylEmbedding_length (w : DP.weylGroupToPerm.range) :
    rootWeylLength Q qb (weylEmbedding w) = rootWeylLength DP db w :=
  rootWeylHom_length DP db Q qb weylEmbedding simpleEmbedding weylEmbedding_simple
    weylEmbedding_injective E6Parabolic.J mem_J_iff_simpleEmbedding w

theorem parabolicEquiv_length (w : DP.weylGroupToPerm.range) :
    rootWeylLength Q qb (parabolicEquiv w).val = rootWeylLength DP db w :=
  weylEmbedding_length w

end Atlas.Chevalley.E6D5

import Atlas.LinearGroups.Triality.RootSubgroups
import Atlas.LinearGroups.Triality.PinnedMatrices

/-! Construction interfaces for the actual folded-root matrix subgroup. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem shortRoot_mem (a : K) : shortRoot F K a ∈ generated F K :=
  Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨a,rfl⟩)))

theorem shortNegativeRoot_mem (a : K) : shortNegativeRoot F K a ∈ generated F K :=
  Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨a,rfl⟩)))

theorem longRoot_mem (a : F) : longRoot F K a ∈ generated F K :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨a,rfl⟩))

theorem longNegativeRoot_mem (a : F) : longNegativeRoot F K a ∈ generated F K :=
  Subgroup.subset_closure (Or.inr ⟨a,rfl⟩)

theorem shortRootSubgroup_le_generated : shortRootSubgroup F K ≤ generated F K := by
  rintro _ ⟨a,rfl⟩
  exact shortRoot_mem F K a.toAdd

theorem shortNegativeRootSubgroup_le_generated :
    shortNegativeRootSubgroup F K ≤ generated F K := by
  rintro _ ⟨a,rfl⟩
  exact shortNegativeRoot_mem F K a.toAdd

theorem longRootSubgroup_le_generated : longRootSubgroup F K ≤ generated F K := by
  rintro _ ⟨a,rfl⟩
  exact longRoot_mem F K a.toAdd

theorem longNegativeRootSubgroup_le_generated :
    longNegativeRootSubgroup F K ≤ generated F K := by
  rintro _ ⟨a,rfl⟩
  exact longNegativeRoot_mem F K a.toAdd

instance nontrivial_group : Nontrivial (Group F K) := by
  apply Function.Injective.nontrivial (f := fun a : K =>
    (⟨shortRoot F K a, shortRoot_mem F K a⟩ : Group F K))
  intro a b h
  exact shortRoot_injective F K (congrArg Subtype.val h)

end Atlas.Triality

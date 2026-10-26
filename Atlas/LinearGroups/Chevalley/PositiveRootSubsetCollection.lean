import Atlas.LinearGroups.Chevalley.RootData.PositiveRootConeClosed
import Atlas.LinearGroups.Chevalley.PositiveRootCollection
import Atlas.GroupTheory.HeightOrderedSubgroupCollection
import Atlas.GroupTheory.OrderedSubgroupParameters

/-! Restricted collection for the actual join of root subgroups in a
cone-closed positive-root subset. The original root heights are retained. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData
open scoped commutatorElement

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

def positiveRootSubsetSubgroup (S : Set {β : ι // b.IsPos β}) :
    Subgroup (WeightCompanion P b O hc hm R) :=
  ⨆ β : S, positiveWeightCompanionRootSubgroup P b O hc hm R β.val

theorem positiveRootSubgroup_le_subset
    (S : Set {β : ι // b.IsPos β}) (β : S) :
    positiveWeightCompanionRootSubgroup P b O hc hm R β.val ≤
      positiveRootSubsetSubgroup P b O hc hm R S :=
  le_iSup (fun γ : S => positiveWeightCompanionRootSubgroup P b O hc hm R γ.val) β

theorem positiveRootSubsetSubgroup_le_witnessed (S : Set {β : ι // b.IsPos β}) :
    positiveRootSubsetSubgroup P b O hc hm R S ≤
      positiveWitnessedWeightCompanionSubgroup P b O hc hm R :=
  iSup_le fun β => positiveWeightCompanionRootSubgroup_le_witnessed P b O hc hm R β.val

variable (hdiamond : SimpleDiamondProducts P b)
include hdiamond

theorem positiveRootSubset_height_commutators
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (α β : S) (hne : α ≠ β) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α.val,
      positiveWeightCompanionRootSubgroup P b O hc hm R β.val⁆ ≤
      ⨆ γ : {γ : S // b.height β.val.val < b.height γ.val.val},
        positiveWeightCompanionRootSubgroup P b O hc hm R γ.val.val := by
  have hne' : α.val ≠ β.val := fun he => hne (Subtype.ext he)
  apply (positiveRootSubgroup_commutator_cone P b O hc hm R hdiamond α.val β.val hne').trans
  apply iSup_le
  intro γ
  let δ : S := ⟨γ.val,hS α.val α.property β.val β.property γ.val γ.property⟩
  exact le_iSup (fun ε : {ε : S // b.height β.val.val < b.height ε.val.val} =>
    positiveWeightCompanionRootSubgroup P b O hc hm R ε.val.val)
      ⟨δ,(positiveIntegralRootCone_height_gt P b γ.property α.val.property β.val.property).2⟩

/-- Every distinct exhaustive nondecreasing-height list in S collects to U_S. -/
theorem positiveRootSubset_orderedProduct_eq_subgroup
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (l : List S) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val.val ≤ b.height γ.val.val))
    (hcover : ∀ β : S, β ∈ l) :
    Atlas.GroupTheory.orderedSubgroupProduct
      (l.map fun β => positiveWeightCompanionRootSubgroup P b O hc hm R β.val) =
        (positiveRootSubsetSubgroup P b O hc hm R S : Set _) :=
  Atlas.GroupTheory.orderedSubgroupProduct_map_eq_iSup_of_height
    (fun β : S => positiveWeightCompanionRootSubgroup P b O hc hm R β.val)
    (fun β : S => b.height β.val.val)
    (positiveRootSubset_height_commutators P b O hc hm R hdiamond S hS)
    l hnodup hsorted hcover

/-- Actual collection supplies one scalar parameter per member of S. -/
theorem positiveRootSubset_exists_parameters
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (l : List S) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val.val ≤ b.height γ.val.val))
    (hcover : ∀ β : S, β ∈ l)
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveRootSubsetSubgroup P b O hc hm R S) :
    ∃ s : S → R, (l.map fun β => weightCompanionRootLiftHom P b O hc hm R
      (positiveRootChosenLift P b O hc hm R β.val) (Multiplicative.ofAdd (s β))).prod = g := by
  have hp : g ∈ Atlas.GroupTheory.orderedSubgroupProduct
      (l.map fun β => positiveWeightCompanionRootSubgroup P b O hc hm R β.val) := by
    rw [positiveRootSubset_orderedProduct_eq_subgroup P b O hc hm R hdiamond S hS
      l hnodup hsorted hcover]
    exact hg
  let f : S → Multiplicative R →* WeightCompanion P b O hc hm R := fun β =>
    weightCompanionRootLiftHom P b O hc hm R (positiveRootChosenLift P b O hc hm R β.val)
  have hp' : g ∈ Atlas.GroupTheory.orderedSubgroupProduct (l.map fun β => (f β).range) := hp
  obtain ⟨s,hs⟩ := (Atlas.GroupTheory.mem_orderedSubgroupProduct_map_range_iff
    f l hnodup g).mp hp'
  exact ⟨fun β => (s β).toAdd,hs⟩

end Atlas.Chevalley

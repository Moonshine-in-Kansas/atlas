import Atlas.LinearGroups.Chevalley.PositiveRootOmission
import Atlas.LinearGroups.Chevalley.PositiveRootCollection
import Atlas.LinearGroups.Chevalley.LiteralPositiveRootRanges
import Atlas.GroupTheory.NormalizerJoin
import Lean.Elab.Tactic.Omega

/-! The omitted subgroup is normalized by the simple root subgroup. Thus U
has actual two-factor decompositions in either order. No Bruhat, uniqueness,
field assumption, or full-group cardinality is asserted. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule Atlas.GroupTheory
open scoped commutatorElement Pointwise

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]
  (hdiamond : SimpleDiamondProducts P b)
include hdiamond

/-- The actual commutator with any retained root subgroup stays in the omitted
subgroup, since every output has height greater than the positive input. -/
theorem simpleRoot_commutator_le_omission (i : b.support)
    (β : {β : ι // b.IsPos β}) (hne : β.val ≠ i.val) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R
        ⟨i.val,b.isPos_of_mem_support i.property⟩,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
        positiveRootOmissionSubgroup P b O hc hm R i := by
  have hne' : (⟨i.val,b.isPos_of_mem_support i.property⟩ : {β : ι // b.IsPos β}) ≠ β := by
    intro he
    exact hne (congrArg Subtype.val he).symm
  apply (positiveRootSubgroup_height_commutators P b O hc hm R hdiamond
    ⟨i.val,b.isPos_of_mem_support i.property⟩ β hne').trans
  apply iSup_le
  intro γ
  apply positiveRootSubgroup_le_omission P b O hc hm R i γ.val
  intro he
  have hh := γ.property
  have hβ : (0 : ℤ) < b.height β.val := β.property
  rw [he,b.height_one_of_mem_support i.property] at hh
  omega

theorem simpleRootSubgroup_le_omission_normalizer (i : b.support) :
    positiveWeightCompanionRootSubgroup P b O hc hm R
      ⟨i.val,b.isPos_of_mem_support i.property⟩ ≤
        Subgroup.normalizer (positiveRootOmissionSubgroup P b O hc hm R i) := by
  rw [positiveRootOmissionSubgroup,Subgroup.iSup_eq_closure,
    Subgroup.le_normalizer_closure_iff]
  intro x hx g hg
  obtain ⟨β,hgβ⟩ := Set.mem_iUnion.mp hg
  rw [← Subgroup.iSup_eq_closure]
  change x * g * x⁻¹ ∈ positiveRootOmissionSubgroup P b O hc hm R i
  have hcomm := simpleRoot_commutator_le_omission P b O hc hm R hdiamond i β.val β.property
    (Subgroup.commutator_mem_commutator hx hgβ)
  have hg' := positiveRootSubgroup_le_omission P b O hc hm R i β.val β.property hgβ
  have hmul := (positiveRootOmissionSubgroup P b O hc hm R i).mul_mem hcomm hg'
  simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hmul

theorem positiveRootOmission_normal_in_witnessed (i : b.support) :
    ((positiveRootOmissionSubgroup P b O hc hm R i).subgroupOf
      (positiveWitnessedWeightCompanionSubgroup P b O hc hm R)).Normal := by
  rw [positiveWitnessedWeightCompanion_eq_omission_sup_simple P b O hc hm R hdiamond i]
  exact normalizerJoin_normal _ _ (simpleRootSubgroup_le_omission_normalizer
    P b O hc hm R hdiamond i)

/-- Every actual element of U is an omitted-subgroup element times X_i(t). -/
theorem positiveWitnessed_exists_omission_mul_X (i : b.support)
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R) :
    ∃ u ∈ positiveRootOmissionSubgroup P b O hc hm R i, ∃ t : R,
      u * weightCompanionX P b O hc hm R i t = g := by
  have hprod : g ∈ (positiveRootOmissionSubgroup P b O hc hm R i : Set (WeightCompanion P b O hc hm R)) *
      (positiveWeightCompanionRootSubgroup P b O hc hm R
        ⟨i.val,b.isPos_of_mem_support i.property⟩ : Set (WeightCompanion P b O hc hm R)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (simpleRootSubgroup_le_omission_normalizer P b O hc hm R hdiamond i)]
    rw [← positiveWitnessedWeightCompanion_eq_omission_sup_simple P b O hc hm R hdiamond i]
    exact hg
  obtain ⟨u,hu,x,hx,hux⟩ := hprod
  rw [← weightCompanionXHom_range_eq_positiveRoot P b O hc hm R hdiamond i] at hx
  obtain ⟨t,rfl⟩ := hx
  exact ⟨u,hu,t.toAdd,hux⟩

/-- Every actual element of U also has the opposite two-factor order. -/
theorem positiveWitnessed_exists_X_mul_omission (i : b.support)
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R) :
    ∃ t : R, ∃ u ∈ positiveRootOmissionSubgroup P b O hc hm R i,
      weightCompanionX P b O hc hm R i t * u = g := by
  have hprod : g ∈ (positiveWeightCompanionRootSubgroup P b O hc hm R
        ⟨i.val,b.isPos_of_mem_support i.property⟩ : Set (WeightCompanion P b O hc hm R)) *
      (positiveRootOmissionSubgroup P b O hc hm R i : Set (WeightCompanion P b O hc hm R)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (simpleRootSubgroup_le_omission_normalizer P b O hc hm R hdiamond i),sup_comm]
    rw [← positiveWitnessedWeightCompanion_eq_omission_sup_simple P b O hc hm R hdiamond i]
    exact hg
  obtain ⟨x,hx,u,hu,hxu⟩ := hprod
  rw [← weightCompanionXHom_range_eq_positiveRoot P b O hc hm R hdiamond i] at hx
  obtain ⟨t,rfl⟩ := hx
  exact ⟨t.toAdd,u,hu,hxu⟩

end Atlas.Chevalley

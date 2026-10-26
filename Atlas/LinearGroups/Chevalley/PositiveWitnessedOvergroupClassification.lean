import Atlas.LinearGroups.Chevalley.PositiveWitnessedOvergroupWords
import Atlas.LinearGroups.Chevalley.PositiveWitnessedStandardParabolic

/-! Every subgroup of the actual full companion containing B is a literally
generated standard parabolic. Its simple set consists of exactly the simple
Tits representatives already in the subgroup. The proof uses actual Bruhat
coverage and reduced-word descent, not an assumed BN-pair classification. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K]

/-- The actual simple representatives belonging to H, as a finite node set. -/
def positiveWitnessedOvergroupSimpleSet
    (H : Subgroup (WeightCompanion P b O hc hm K)) : Finset b.support :=
  Finset.univ.filter (fun i => weightCompanionWeyl P b O hc hm K i 1 ∈ H)

theorem standardParabolic_overgroupSimpleSet_le
    (H : Subgroup (WeightCompanion P b O hc hm K))
    (hB : positiveWitnessedTorusJoin P b O hc hm K ≤ H) :
    positiveWitnessedStandardParabolic P b O hc hm K
      (positiveWitnessedOvergroupSimpleSet P b O hc hm K H) ≤ H := by
  change Subgroup.closure _ ≤ H
  rw [Subgroup.closure_le]
  rintro g (hg | ⟨i, hi, rfl⟩)
  · exact hB hg
  · exact (Finset.mem_filter.mp hi).2

variable [Fintype κ]

/-- B-overgroups are standard parabolics for the actual generated companion.
The finite orbit-index and diamond hypotheses enter only through the existing
Bruhat/canonical-cell interfaces; no finite-field or perfectness is used. -/
theorem positiveWitnessedOvergroup_eq_standardParabolic
    (hdiamond : SimpleDiamondProducts P b)
    (H : Subgroup (WeightCompanion P b O hc hm K))
    (hB : positiveWitnessedTorusJoin P b O hc hm K ≤ H) :
    H = positiveWitnessedStandardParabolic P b O hc hm K
      (positiveWitnessedOvergroupSimpleSet P b O hc hm K H) := by
  apply le_antisymm _ (standardParabolic_overgroupSimpleSet_le P b O hc hm K H hB)
  intro g hg
  obtain ⟨w, hw⟩ := exists_mem_positiveWitnessedWeylCell P b O hc hm K hdiamond g
  have hn : (weightCompanionTitsLift P b O hc hm K w).val ∈ H := by
    obtain ⟨a, ha, c, hc', heq⟩ := DoubleCoset.mem_doubleCoset.mp hw
    rw [heq] at hg
    exact (H.mul_mem_cancel_left (hB ha)).mp
      ((H.mul_mem_cancel_right (hB hc')).mp hg)
  obtain ⟨l, heq, hlen⟩ := root_reduced_representatives P b w
  change rootWeylWord P b l = w at heq
  have hred : IsReducedRootWord P b l := by
    change rootWeylLength P b (rootWeylWord P b l) = l.length
    rw [heq]
    exact hlen.symm
  have hperm : weightCompanionNRootPermHom P b O hc hm K
      (weightCompanionTitsLift P b O hc hm K w) = (rootWeylWord P b l).val := by
    rw [weightCompanionNRootPermHom_titsLift, heq]
  have hletters := weightCompanionWeyl_mem_of_reduced_word_lift_mem
    P b O hc hm K H hB l hred (weightCompanionTitsLift P b O hc hm K w) hn hperm
  have hpar : w ∈ rootParabolicSubgroup P b
      (positiveWitnessedOvergroupSimpleSet P b O hc hm K H) := by
    apply (rootParabolic_mem_iff_word P b _ w).mpr
    refine ⟨l, ?_, heq⟩
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hletters i hi⟩
  exact parabolicCells_subset_standardParabolic P b O hc hm K hdiamond _ ⟨w, hpar, hw⟩

end Atlas.Chevalley

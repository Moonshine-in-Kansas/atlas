import Atlas.LinearGroups.Chevalley.RootData.ParabolicSimpleMembership
import Atlas.LinearGroups.Chevalley.PositiveWitnessedOvergroupClassification
import Mathlib.Order.Atoms

/-! Inclusion and maximality for literally generated standard parabolics of
the actual companion. The field may be infinite. This does not assert that
the action on all Borel cosets is quasiprimitive. -/
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

theorem positiveWitnessedStandardParabolic_mono
    {J L : Finset b.support} (h : J ⊆ L) :
    positiveWitnessedStandardParabolic P b O hc hm K J ≤
      positiveWitnessedStandardParabolic P b O hc hm K L := by
  apply Subgroup.closure_mono
  rintro g (hg | ⟨i, hi, rfl⟩)
  · exact Or.inl hg
  · exact Or.inr ⟨i, h hi, rfl⟩

variable [Fintype κ]

theorem weightCompanionWeyl_mem_standardParabolic_iff
    (hdiamond : SimpleDiamondProducts P b) (J : Finset b.support) (i : b.support) :
    weightCompanionWeyl P b O hc hm K i 1 ∈
      positiveWitnessedStandardParabolic P b O hc hm K J ↔ i ∈ J := by
  have hcell : weightCompanionWeyl P b O hc hm K i 1 ∈
      positiveWitnessedWeylCell P b O hc hm K (simpleWeylReflection P b i) := by
    change weightCompanionWeyl P b O hc hm K i 1 ∈
      DoubleCoset.doubleCoset
        (weightCompanionTitsLift P b O hc hm K (simpleWeylReflection P b i)).val _ _
    rw [weightCompanionTitsLift_simple P b O hc hm K hdiamond]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  exact (mem_standardParabolic_iff_of_mem_weylCell P b O hc hm K hdiamond J
    (simpleWeylReflection P b i) (weightCompanionWeyl P b O hc hm K i 1) hcell).trans
      (simpleWeylReflection_mem_rootParabolic_iff P b J i)

theorem positiveWitnessedStandardParabolic_le_iff
    (hdiamond : SimpleDiamondProducts P b) (J L : Finset b.support) :
    positiveWitnessedStandardParabolic P b O hc hm K J ≤
      positiveWitnessedStandardParabolic P b O hc hm K L ↔ J ⊆ L := by
  constructor
  · intro h i hi
    exact (weightCompanionWeyl_mem_standardParabolic_iff P b O hc hm K hdiamond L i).mp
      (h (weightCompanionWeyl_mem_standardParabolic P b O hc hm K J i hi))
  · exact positiveWitnessedStandardParabolic_mono P b O hc hm K

theorem positiveWitnessedStandardParabolic_univ
    (hdiamond : SimpleDiamondProducts P b) :
    positiveWitnessedStandardParabolic P b O hc hm K Finset.univ = ⊤ := by
  have he := positiveWitnessedOvergroup_eq_standardParabolic
    P b O hc hm K hdiamond ⊤ le_top
  have hJ : positiveWitnessedOvergroupSimpleSet P b O hc hm K ⊤ = Finset.univ := by
    ext i
    simp [positiveWitnessedOvergroupSimpleSet]
  rw [hJ] at he
  exact he.symm

theorem positiveWitnessedStandardParabolic_eq_top_iff
    (hdiamond : SimpleDiamondProducts P b) (J : Finset b.support) :
    positiveWitnessedStandardParabolic P b O hc hm K J = ⊤ ↔ J = Finset.univ := by
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro i
    apply (weightCompanionWeyl_mem_standardParabolic_iff P b O hc hm K hdiamond J i).mp
    rw [h]
    exact Subgroup.mem_top _
  · rintro rfl
    exact positiveWitnessedStandardParabolic_univ P b O hc hm K hdiamond

/-- Omitting one simple node gives a maximal proper actual subgroup. -/
theorem positiveWitnessedStandardParabolic_erase_isCoatom
    (hdiamond : SimpleDiamondProducts P b) (i : b.support) :
    IsCoatom (positiveWitnessedStandardParabolic P b O hc hm K (Finset.univ.erase i)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have he := (positiveWitnessedStandardParabolic_eq_top_iff
      P b O hc hm K hdiamond (Finset.univ.erase i)).mp h
    have hi : i ∈ Finset.univ.erase i := he.symm ▸ Finset.mem_univ i
    exact Finset.notMem_erase i _ hi
  · intro H hlt
    have hB : positiveWitnessedTorusJoin P b O hc hm K ≤ H :=
      (positiveWitnessedTorusJoin_le_standardParabolic P b O hc hm K _).trans hlt.le
    let J := positiveWitnessedOvergroupSimpleSet P b O hc hm K H
    have hH : H = positiveWitnessedStandardParabolic P b O hc hm K J :=
      positiveWitnessedOvergroup_eq_standardParabolic P b O hc hm K hdiamond H hB
    have hsub : Finset.univ.erase i ⊆ J :=
      (positiveWitnessedStandardParabolic_le_iff P b O hc hm K hdiamond _ J).mp
        (by rw [← hH]; exact hlt.le)
    have hJ : J = Finset.univ := by
      by_cases hi : i ∈ J
      · apply Finset.eq_univ_of_forall
        intro j
        by_cases hji : j = i
        · exact hji.symm ▸ hi
        · exact hsub (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      · exfalso
        apply hlt.not_ge
        rw [hH]
        apply positiveWitnessedStandardParabolic_mono P b O hc hm K
        intro j hj
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j⟩
        intro hji
        exact hi (hji ▸ hj)
    rw [hH, hJ]
    exact positiveWitnessedStandardParabolic_univ P b O hc hm K hdiamond

end Atlas.Chevalley

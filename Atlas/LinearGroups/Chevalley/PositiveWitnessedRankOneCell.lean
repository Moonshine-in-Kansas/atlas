import Atlas.LinearGroups.Chevalley.WeightCompanionRankOneCell
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusJoin
import Mathlib.GroupTheory.DoubleCoset

/-! The negative simple-root family lies in B ∪ B n_i B over a field,
where B is the actual existing U*T join. This is a rank-one inclusion only;
no global Bruhat decomposition, disjointness or counting is assumed. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

/-- The identity normalizer lift realizes every literal positive simple-root
element in the all-witness subgroup, without root-choice coherence. -/
theorem weightCompanionX_mem_positiveWitnessed (i : b.support) (t : R) :
    weightCompanionX P b O hc hm R i t ∈
      positiveWitnessedWeightCompanionSubgroup P b O hc hm R := by
  let L : WeightCompanionRootLift P b O hc hm R i.val :=
    ⟨i, 1, by simp⟩
  have h := rootLiftHom_mem_positiveWitnessedWeightCompanionSubgroup
    P b O hc hm R (b.isPos_of_mem_support i.property) L (Multiplicative.ofAdd t)
  change (1 : WeightCompanion P b O hc hm R) *
    weightCompanionX P b O hc hm R i t * 1⁻¹ ∈ _ at h
  simpa only [one_mul, inv_one, mul_one] using h

theorem weightCompanionX_mem_positiveWitnessedTorusJoin (i : b.support) (t : R) :
    weightCompanionX P b O hc hm R i t ∈
      positiveWitnessedTorusJoin P b O hc hm R :=
  (show positiveWitnessedWeightCompanionSubgroup P b O hc hm R ≤
    positiveWitnessedTorusJoin P b O hc hm R from le_sup_left)
      (weightCompanionX_mem_positiveWitnessed P b O hc hm R i t)

theorem weightCompanionTorus_mem_positiveWitnessedTorusJoin (i : b.support) (a : Rˣ) :
    weightCompanionTorus P b O hc hm R i a ∈
      positiveWitnessedTorusJoin P b O hc hm R :=
  (show weightCompanionTorusSubgroup P b O hc hm R ≤
    positiveWitnessedTorusJoin P b O hc hm R from le_sup_right)
      (Subgroup.subset_closure ⟨i, a, rfl⟩)

/-- Every unit parameter belongs to the literal simple-reflection double coset. -/
theorem weightCompanionY_unit_mem_positiveWitnessed_doubleCoset
    (i : b.support) (a : Rˣ) :
    weightCompanionY P b O hc hm R i (↑a : R) ∈
      DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm R i 1)
        (positiveWitnessedTorusJoin P b O hc hm R)
        (positiveWitnessedTorusJoin P b O hc hm R) := by
  apply DoubleCoset.mem_doubleCoset.mpr
  refine ⟨weightCompanionX P b O hc hm R i (↑(a⁻¹) : R) *
      weightCompanionTorus P b O hc hm R i (-a⁻¹), ?_,
    weightCompanionX P b O hc hm R i (↑(a⁻¹) : R), ?_, ?_⟩
  · exact (positiveWitnessedTorusJoin P b O hc hm R).mul_mem
      (weightCompanionX_mem_positiveWitnessedTorusJoin P b O hc hm R i _)
      (weightCompanionTorus_mem_positiveWitnessedTorusJoin P b O hc hm R i _)
  · exact weightCompanionX_mem_positiveWitnessedTorusJoin P b O hc hm R i _
  · exact weightCompanionY_unit_eq_rankOne_product P b O hc hm R i a

/-- Nonzero field parameters lie in B n_i B for the existing full companion. -/
theorem weightCompanionY_mem_positiveWitnessed_doubleCoset_of_ne_zero
    (K : Type*) [Field K] (i : b.support) (t : K) (ht : t ≠ 0) :
    weightCompanionY P b O hc hm K i t ∈
      DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) :=
  weightCompanionY_unit_mem_positiveWitnessed_doubleCoset
    P b O hc hm K i (Units.mk0 t ht)

/-- The rank-one field dichotomy, expressed without a global Bruhat claim. -/
theorem weightCompanionY_mem_positiveWitnessed_or_doubleCoset
    (K : Type*) [Field K] (i : b.support) (t : K) :
    weightCompanionY P b O hc hm K i t ∈ positiveWitnessedTorusJoin P b O hc hm K ∨
      weightCompanionY P b O hc hm K i t ∈
        DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
          (positiveWitnessedTorusJoin P b O hc hm K)
          (positiveWitnessedTorusJoin P b O hc hm K) := by
  by_cases ht : t = 0
  · left
    subst t
    have hzero : weightCompanionY P b O hc hm K i 0 = 1 :=
      (weightCompanionYHom P b O hc hm K i).map_one
    rw [hzero]
    exact (positiveWitnessedTorusJoin P b O hc hm K).one_mem
  · exact Or.inr (weightCompanionY_mem_positiveWitnessed_doubleCoset_of_ne_zero
      P b O hc hm K i t ht)

end Atlas.Chevalley

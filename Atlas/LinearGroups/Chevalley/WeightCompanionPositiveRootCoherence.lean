import Atlas.LinearGroups.Chevalley.WeightCompanionRootLiftReducedPrefix
import Atlas.LinearGroups.Chevalley.WeightCompanionReducedRootMarks

/-! Positive-root subgroups are independent of every retained lift choice.
The proof combines the actual local marked braids with the already proved
normalizer quotient. No pointwise normalization of root parameters is asserted. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
open Atlas.GroupTheory.ReducedWords

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

/-- For the same positive root, the literal root subgroup is independent of
the originating simple root and of the full normalizer lift. -/
theorem weightCompanionRootLiftSubgroup_eq_of_positive
    (hdiamond : SimpleDiamondProducts P b) {β : ι} (hβ : b.IsPos β)
    (L L' : WeightCompanionRootLift P b O hc hm R β) :
    weightCompanionRootLiftSubgroup P b O hc hm R L =
      weightCompanionRootLiftSubgroup P b O hc hm R L' := by
  obtain ⟨p, hp, _, hperm, _⟩ :=
    weightCompanionRootLift_reducedPrefix P b O hc hm R hdiamond hβ L
  obtain ⟨q, hq, _, hperm', _⟩ :=
    weightCompanionRootLift_reducedPrefix P b O hc hm R hdiamond hβ L'
  rw [weightCompanionRootLiftSubgroup_eq_wordEval P b O hc hm R hdiamond L p hperm,
    weightCompanionRootLiftSubgroup_eq_wordEval P b O hc hm R hdiamond L' q hperm']
  apply weightCompanion_reducedPrefix_rootSubgroup_eq P b O hc hm R
    hdiamond p q hp hq L.simple L'.simple
  · rw [hperm, L.root_eq]
    exact hβ
  · rw [hperm, hperm', L.root_eq, L'.root_eq]

end Atlas.Chevalley

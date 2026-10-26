import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionGeneration
import Atlas.LinearGroups.Chevalley.WeightCompanionRootPermutation

/-! The actual extended Weyl subgroup has the full root-permutation image.
This identifies its image, not its kernel. Source candidate, not yet checked. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem simpleRootPermutationSubgroup_eq_weylImage :
    simpleRootPermutationSubgroup P b = P.weylGroupToPerm.range :=
  RootData.simpleReflectionClosure_eq_weylImage P b

variable (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

theorem weightCompanionNRootPermHom_range_eq_weylImage :
    (weightCompanionNRootPermHom P b O hclosed hmin R).range =
      P.weylGroupToPerm.range := by
  rw [weightCompanionNRootPermHom_range, simpleRootPermutationSubgroup_eq_weylImage]

/-- A literal element of N carries some simple-root coordinate line to every
specified root coordinate line. This is not yet root-subgroup conjugation. -/
theorem weightCompanion_exists_simpleRoot_lift (i : ι) :
    ∃ j : b.support,
      ∃ n : weightCompanionExtendedWeylSubgroup P b O hclosed hmin R,
        weightCompanionNRootPermHom P b O hclosed hmin R n j.val = i := by
  obtain ⟨j, w, hw, hwi⟩ := RootData.exists_simpleRoot_word P b i
  have hw' : w ∈ (weightCompanionNRootPermHom P b O hclosed hmin R).range := by
    rw [weightCompanionNRootPermHom_range]
    exact hw
  obtain ⟨n, hn⟩ := hw'
  refine ⟨j, n, ?_⟩
  rw [hn]
  exact hwi

end Atlas.Chevalley
